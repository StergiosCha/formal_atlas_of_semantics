"""Typed feedback extraction — coqc's complaint as structure, not stderr.

A3_PLAN's rule: never paste raw compiler output back into the prompt.
Parse it into typed signals; the same structure is the student-facing
lesson and the model-facing repair signal, and keeping raw available
alongside is deliberate — it is ablation arm A1 in experiment E2.

Coq 8.20 error messages are regex-stable; each parser below is anchored
to the exact phrasing coqc emits. Anything unrecognized falls through to
kind=unclassified with the raw tail, so no failure mode is silently
swallowed.
"""
import re

_PARSERS = [
    ("unbound_identifier",
     re.compile(r"The reference ([\w.']+) was not found in the current\s+environment"),
     lambda m: {"name": m.group(1)}),
    ("unbound_notation",
     re.compile(r'Unknown interpretation for notation "([^"]+)"'),
     lambda m: {"notation": m.group(1)}),
    ("type_mismatch",
     re.compile(r'The term "(.{1,200}?)" has type\s+"(.{1,300}?)"\s+while it is expected to have type\s+"(.{1,300}?)"', re.S),
     lambda m: {"term": " ".join(m.group(1).split()),
                "actual": " ".join(m.group(2).split()),
                "expected": " ".join(m.group(3).split())}),
    ("illegal_application",
     re.compile(r'Illegal application.*?The term "(.{1,200}?)" of type\s+"(.{1,300}?)"\s+cannot be applied to', re.S),
     lambda m: {"head": " ".join(m.group(1).split()),
                "head_type": " ".join(m.group(2).split())}),
    ("unsolved_goals",
     re.compile(r"(?:Attempt to save an incomplete proof|There are pending proofs|.*?unsolved goals)", re.S),
     lambda m: {}),
    ("tactic_failure",
     re.compile(r"(?:Tactic failure|No applicable tactic|Cannot solve this goal|tauto failed|firstorder failed)(?::\s*(.{1,200}))?"),
     lambda m: {"detail": (m.group(1) or "").strip()}),
    ("universe_inconsistency",
     re.compile(r"Universe inconsistency"),
     lambda m: {}),
    ("syntax_error",
     re.compile(r"Syntax error:\s*(.{1,200})"),
     lambda m: {"detail": m.group(1).strip()}),
    ("missing_import",
     re.compile(r"Cannot find a physical path bound to logical path\s+([\w.]+)"),
     lambda m: {"module": m.group(1)}),
    ("timeout",
     re.compile(r"timeout after (\d+)s"),
     lambda m: {"seconds": int(m.group(1))}),
    ("bad_import",
     re.compile(r"bad import: (.+)"),
     lambda m: {"import": m.group(1).strip()}),
]

_LOC = re.compile(r'File "[^"]*", line (\d+), characters ([\d-]+):')


def extract(coqc_output: str) -> list[dict]:
    """coqc stdout+stderr -> list of typed signals, in order of appearance."""
    out = []
    # Split on location headers so multi-error output yields one signal each.
    parts = _LOC.split(coqc_output)
    # parts = [pre, line1, chars1, body1, line2, chars2, body2, ...]
    chunks = ([(None, parts[0])] +
              [(int(parts[i]), parts[i + 2]) for i in range(1, len(parts) - 2, 3)])
    for line, body in chunks:
        if not any(k in body for k in ("Error", "timeout", "bad import")):
            continue
        for kind, rx, fields in _PARSERS:
            m = rx.search(body)
            if m:
                sig = {"kind": kind, **fields(m)}
                if line:
                    sig["line"] = line
                out.append(sig)
                break
        else:
            err = body.split("Error:", 1)[-1].strip()
            if err:
                sig = {"kind": "unclassified", "detail": " ".join(err.split())[:400]}
                if line:
                    sig["line"] = line
                out.append(sig)
    return out


def render(signals: list[dict], vocabulary_hint: str = "") -> str:
    """Typed signals -> the repair prompt (ablation arm A2/A3). Speaks about
    the theory, not about compiler internals."""
    if not signals:
        return "The checker rejected the snippet but produced no parseable error."
    lines = []
    for s in signals:
        k = s["kind"]
        at = f" (line {s['line']})" if s.get("line") else ""
        if k == "unbound_identifier":
            lines.append(
                f"- `{s['name']}` does not exist in this theory's vocabulary{at}. "
                "Do not invent constants: restate the claim using only what the "
                "theory defines, or classify it NOT-STATABLE with that reason.")
        elif k == "type_mismatch":
            lines.append(
                f"- Type mismatch{at}: `{s['term']}` has type `{s['actual']}` "
                f"but `{s['expected']}` is required. Re-examine how the theory "
                "types this construct; do not coerce blindly.")
        elif k == "illegal_application":
            lines.append(
                f"- `{s['head']}` : `{s['head_type']}` is applied to an argument "
                f"it cannot take{at}. Check the argument order and arity the "
                "theory actually uses.")
        elif k == "unsolved_goals":
            lines.append(
                "- The statement compiled but the proof is incomplete. Either "
                "finish it with the listed tactic bank or, if the claim may be "
                "false, draft the countermodel instead.")
        elif k == "tactic_failure":
            lines.append(
                f"- Tactic failed{at}: {s.get('detail') or 'no detail'}. Try a "
                "different decomposition; if the claim resists systematically, "
                "consider that it may be REFUTED and draft a countermodel.")
        elif k == "missing_import":
            mod = s["module"]
            fix = ""
            for pfx in ("atlas.", "shallow.", "extras.", "deep.", "ttr_mtt."):
                if mod.startswith(pfx):
                    fix = (f" Drop the `{pfx[:-1]}` prefix — the library roots "
                           f"map to the empty logical prefix; write "
                           f"`Require Import {mod[len(pfx):]}.`")
                    break
            lines.append(
                f"- Module `{mod}` is not importable.{fix}"
                if fix else
                f"- Module `{mod}` is not importable. Use the fully qualified "
                "atlas names exactly as given (probabilistic.RSA, montague.PTQ, "
                "dynamic.DPL, inquisitive.InqB, mtt_ranta.MTT, mtt_ranta.Ranta, "
                "mtt_ranta.DTS, type_logical.Lambek, categorical.DisCoCat).")
        elif k == "timeout":
            lines.append(
                f"- Compilation exceeded {s['seconds']}s. Avoid vm_compute on "
                "large terms; state a smaller instance.")
        elif k == "universe_inconsistency":
            lines.append("- Universe inconsistency: the encoding over-quantifies. "
                         "Lower the universe demands (no Type where Prop serves).")
        else:
            lines.append(f"- {s.get('detail', k)}{at}")
    if vocabulary_hint:
        lines.append(f"\nAvailable vocabulary (excerpt): {vocabulary_hint}")
    return "The Coq checker rejected the draft for these reasons:\n" + "\n".join(lines)
