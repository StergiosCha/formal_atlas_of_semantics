"""Semantics Workbench — draft-and-check loop (skeleton).

Requires: pip install anthropic requests
Env: ANTHROPIC_API_KEY; CHECKER_URL (default http://localhost:8477)

Usage:
  python3 loop.py "<paper fragment or claim to formalize>"
"""
import os
import sys

import requests
import anthropic

CHECKER = os.environ.get("CHECKER_URL", "http://localhost:8477")
MODEL = os.environ.get("WORKBENCH_MODEL", "claude-fable-5-1")
MAX_ROUNDS = int(os.environ.get("WORKBENCH_ROUNDS", "6"))

HERE = os.path.dirname(os.path.abspath(__file__))
POLICY = open(os.path.join(HERE, "policy.md")).read()

DRAFT_PROMPT = """{policy}

## Task

Formalize the following, per the protocol. Return ONLY a JSON object:
{{"imports": [...], "code": "<coq>", "audit": ["<theorem names>"],
  "notes": "<one paragraph: what you proved/refuted/re-typed>"}}

## Input

{task}

## Previous attempt feedback (empty on the first round)

{feedback}
"""


def extract_json(text: str) -> dict:
    import json, re
    m = re.search(r"\{.*\}", text, re.S)
    return json.loads(m.group(0)) if m else {}


def main() -> None:
    task = sys.argv[1]
    client = anthropic.Anthropic()
    feedback = ""
    for round_no in range(1, MAX_ROUNDS + 1):
        msg = client.messages.create(
            model=MODEL,
            max_tokens=8000,
            messages=[{"role": "user", "content": DRAFT_PROMPT.format(
                policy=POLICY, task=task, feedback=feedback)}],
        )
        draft = extract_json(msg.content[0].text)
        if not draft.get("code"):
            feedback = "Your reply contained no JSON code block."
            continue
        resp = requests.post(f"{CHECKER}/check", json={
            "code": draft["code"],
            "imports": draft.get("imports", []),
            "audit": draft.get("audit", []),
        }, timeout=120).json()
        if resp["ok"]:
            print("VERIFIED by Coq (round", round_no, ")")
            print("audit:", resp["audit"])
            print("notes:", draft.get("notes", ""))
            print(draft["code"])
            return
        feedback = f"coqc failed:\n{resp['output'][-4000:]}"
        print(f"round {round_no}: checker rejected, iterating...")
    print("UNVERIFIED after", MAX_ROUNDS, "rounds. Last error:")
    print(feedback)


if __name__ == "__main__":
    main()
