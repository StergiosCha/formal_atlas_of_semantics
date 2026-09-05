"""Semantics Workbench — the draft-and-check loop, multi-model.

The iron rule everywhere: the model drafts, coqc disposes. No model text
ever becomes a verdict; the verdict is the compiler's, and every round is
logged to runs/*.jsonl — that log is the research dataset (A3_PLAN,
"The research output nobody else has").

Feedback arms (experiment E2 in A3_PLAN — pick with --feedback):
  none   A0  independent resample, no feedback
  raw    A1  the old behaviour: coqc output tail pasted back
  typed  A2  feedback.py's structured signals (default)

Usage:
  export AZURE_AI_KEY=...            # never stored in the repo
  python3 loop.py "claim in English" --imports probabilistic.RSA
  python3 loop.py "claim" --model claude-opus-5 --feedback raw
  python3 loop.py "claim" --compare  # whole roster, one table
Checker: local coqc by default; --checker http://host:8477 uses the service.
"""
import argparse
import datetime
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_local                      # noqa: E402
import feedback as fb                   # noqa: E402
import providers                        # noqa: E402

POLICY = open(os.path.join(HERE, "policy.md")).read()
RUNS = os.path.join(HERE, "runs")
try:
    SIGNATURES = json.load(open(os.path.join(HERE, "signatures.json")))
except FileNotFoundError:
    SIGNATURES = {}


def vocabulary(imports: list[str]) -> str:
    """The imported theories' real names, so the drafter never guesses. This
    is the signature manifest doing its job (A3_PLAN, NOT-STATABLE tier 1)."""
    parts = []
    for imp in imports:
        s = SIGNATURES.get(imp)
        if not s:
            continue
        parts.append(f"### {imp} — definitions\n" + ", ".join(s["definitions"])
                     + f"\n### {imp} — proved theorems\n"
                     + ", ".join(s["theorems"][:150]))
    return "\n".join(parts)

DRAFT_PROMPT = """{policy}

## Task

Formalize the following against the atlas, per the protocol. The atlas
theories are imported by qualified name (probabilistic.RSA, montague.PTQ,
dynamic.DPL, inquisitive.InqB, mtt_ranta.MTT, mtt_ranta.Ranta,
mtt_ranta.DTS, type_logical.Lambek, categorical.DisCoCat).
Those are the FULL names — never prefix them with `atlas.` (the library
root maps to the empty logical prefix; `atlas.montague.PTQ` does not exist).
Open the scopes your notation needs (e.g. RSA's rationals want
`Require Import QArith. Local Open Scope Q_scope.`).
Return ONLY a JSON object:
{{"imports": [...], "code": "<coq>", "audit": ["<theorem names>"],
  "bucket_guess": "PROVED|REFUTED|NEEDS_ASSUMPTION|NOT_STATABLE",
  "notes": "<one paragraph>"}}

## Input

{task}

## The imported theories' actual vocabulary (do not invent names outside it)

{vocabulary}

## Checker feedback on your previous attempt (empty on the first round)

{feedback}
"""


def extract_json(text: str) -> dict:
    """Models fence their JSON, leave prose around it, and put raw newlines
    inside string values; strict=False tolerates the control characters."""
    candidates = []
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, re.S)
    if fence:
        candidates.append(fence.group(1))
    m = re.search(r"\{.*\}", text, re.S)
    if m:
        candidates.append(m.group(0))
    for c in candidates:
        try:
            return json.loads(c, strict=False)
        except json.JSONDecodeError:
            continue
    return {}


def clean_imports(imports: list) -> list[str]:
    """`["Require Import montague.PTQ."]` -> `["montague.PTQ"]` — models keep
    handing back the whole vernacular sentence."""
    out = []
    for i in imports or []:
        i = re.sub(r"^\s*(?:From\s+\S+\s+)?Require\s+(?:Import|Export)\s+",
                   "", str(i)).strip().rstrip(".").strip()
        for pfx in ("atlas.", "shallow.", "extras.", "deep.", "ttr_mtt."):
            if i.startswith(pfx):
                i = i[len(pfx):]
        if i and i not in out:
            out.append(i)
    return out


def run_checker(url: str | None, draft: dict) -> dict:
    if url:
        import urllib.request
        req = urllib.request.Request(
            url.rstrip("/") + "/check",
            data=json.dumps({"code": draft["code"],
                             "imports": draft.get("imports", []),
                             "audit": draft.get("audit", [])}).encode(),
            headers={"content-type": "application/json"})
        with urllib.request.urlopen(req, timeout=120) as r:
            return json.load(r)
    return check_local.check(draft["code"], draft.get("imports"),
                             draft.get("audit"))


def one_run(task: str, model: str, arm: str, rounds: int,
            imports_hint: list[str], checker_url: str | None,
            log) -> dict:
    """One claim x one model -> final state dict (also fully logged)."""
    fb_text = ""
    state = {"model": model, "arm": arm, "rounds": 0, "bucket": None,
             "audit": {}, "signals": []}
    for rnd in range(1, rounds + 1):
        state["rounds"] = rnd
        try:
            reply = providers.chat(model, [{
                "role": "user",
                "content": DRAFT_PROMPT.format(
                    policy=POLICY, task=task, feedback=fb_text,
                    vocabulary=vocabulary(imports_hint) or "(no hint)")}])
        except providers.ModelError as e:
            state["bucket"] = "MODEL_ERROR"
            state["error"] = str(e)[:300]
            log(rnd, None, None, state)
            return state
        draft = extract_json(reply)
        draft["imports"] = clean_imports(draft.get("imports")) or imports_hint
        if not draft.get("code"):
            fb_text = "Your reply contained no parseable JSON with a code field."
            log(rnd, draft, None, state)
            continue
        resp = run_checker(checker_url, draft)
        signals = fb.extract(resp["output"]) if not resp["ok"] else []
        log(rnd, draft, {"ok": resp["ok"], "audit": resp.get("audit", {}),
                         "signals": signals}, state)
        if resp["ok"]:
            # Iron rule: a bucket is only VERIFIED if Coq audited a theorem.
            # A comment-only or theorem-free draft compiles trivially — that
            # is the model issuing a verdict, and it gets labeled as exactly
            # that (two-tier rule, A3_PLAN: NOT-STATABLE mechanism).
            state["audit"] = resp["audit"]
            state["notes"] = draft.get("notes", "")
            state["code"] = draft["code"]
            if resp["audit"]:
                closed = all(v == "closed" for v in resp["audit"].values())
                state["bucket"] = draft.get("bucket_guess") or "PROVED"
                if state["bucket"] == "PROVED" and not closed:
                    state["bucket"] = "NEEDS_ASSUMPTION"
            else:
                guess = draft.get("bucket_guess") or "UNKNOWN"
                state["bucket"] = f"{guess}_MODEL_CLAIMED_UNVERIFIED"
            return state
        state["signals"] = [s["kind"] for s in signals]
        if arm == "none":
            fb_text = ""
        elif arm == "raw":
            fb_text = f"coqc failed:\n{resp['output'][-4000:]}"
        else:
            fb_text = fb.render(signals)
    state["bucket"] = f"NOT_STATED_AFTER_{rounds}_ATTEMPTS"
    return state


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("task")
    ap.add_argument("--model", default=providers.POLICY["first_draft"])
    ap.add_argument("--compare", action="store_true",
                    help="run every drafter in the roster")
    ap.add_argument("--feedback", choices=["none", "raw", "typed"],
                    default="typed")
    ap.add_argument("--rounds", type=int, default=providers.POLICY["max_rounds"])
    ap.add_argument("--imports", nargs="*", default=[])
    ap.add_argument("--checker", default=None,
                    help="checker URL; default = local coqc")
    a = ap.parse_args()

    os.makedirs(RUNS, exist_ok=True)
    stamp = datetime.datetime.now()
    logpath = os.path.join(RUNS, stamp.strftime("%Y%m%d") + ".jsonl")
    logf = open(logpath, "a")

    def log(model):
        def _log(rnd, draft, check, state):
            logf.write(json.dumps({
                "ts": datetime.datetime.now().isoformat(timespec="seconds"),
                "task": a.task, "model": model, "arm": a.feedback,
                "round": rnd, "draft": draft, "check": check,
            }, ensure_ascii=False) + "\n")
            logf.flush()
        return _log

    models = ([m["deployment"] for m in providers.CFG["roster"]
               if m["role"] == "drafter"] if a.compare else [a.model])
    results = []
    for m in models:
        r = one_run(a.task, m, a.feedback, a.rounds, a.imports,
                    a.checker, log(m))
        results.append(r)
        print(f"{m:24s} {r['bucket']:32s} rounds={r['rounds']} "
              f"audit={r.get('audit') or '—'}"
              + (f"  [{r.get('error','')}]" if r.get("error") else ""))
    if len(results) == 1 and results[0].get("code"):
        print("\n--- final Coq (compiler-accepted) ---\n" + results[0]["code"])
        print("\nnotes:", results[0].get("notes", ""))
    print(f"\nlog: {logpath}")


if __name__ == "__main__":
    main()
