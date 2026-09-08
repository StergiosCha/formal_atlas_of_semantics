# Paper formality rubric (P0–P5)

Graded 2026-09-06, FROZEN. This scale measures the paper's INTRINSIC formality
— how formal the work is on its own pages — and is orthogonal to the atlas
evidence ladder F0–F5 (surveyed → sourced → designed → piloted → formalized →
verified), which measures how far the paper has traveled through OUR pipeline.
The project's central table is formality × outcome: what happens to papers at
each formality stratum when pushed through a proof assistant.

Grading method: two independent graders per paper (rubric + title/abstract-level
knowledge of the work, checking the on-disk PDF when unsure), disagreements
settled by a third judge shown both rationales. Stored in formality.json with
per-paper rationale and confidence; never recomputed by consolidate.py.

## The scale

- **P0 — discursive.** No definitions, no formalism; the argument lives
  entirely in prose. Anchors: Derrida *Of Grammatology*; Heidegger *Being and
  Time*; Ahmed *Cultural Politics of Emotion*.
- **P1 — systematic prose.** Explicit diagnostics, worked examples, taxonomies
  — but no formal apparatus. Anchors: Grice 1975 *Logic and Conversation*;
  Rosch 1978; Austin 1962.
- **P2 — semi-formal.** Regimented definitions and principles, occasional
  notation, no worked calculus or model theory. Anchors: Horn 1984; Clark
  1996 *Using Language*; Fillmore 1976.
- **P3 — formal fragments.** Real formalism (lambda terms, model definitions,
  derivations) in parts of a mostly-prose argument. Anchors: Kratzer 1996
  *Severing the External Argument*; Carlson 1977; Stalnaker 1968.
- **P4 — full formal system.** The paper's core is a defined calculus, logic,
  or model theory with derivations/proofs carried through. Anchors: Church
  1940; Steedman 2000 *The Syntactic Process*; Groenendijk & Stokhof 1984;
  Luo 2011; Shan 2001; Charlow 2014.
- **P5 — machine-checked.** The paper ships with (or is) a verified artifact
  in a proof assistant. Anchor: Chatzikyriakidis & Luo, *Natural Language
  Inference in Coq*.

## Tie-breakers

- Grade the PAPER, not the field or the author's other work.
- Books: grade the formal core if the book HAS one (Steedman P4), the prose if
  it doesn't (Tomasello P1).
- A formal appendix bolted onto a prose argument: P3, not P4.
- Experimental papers: grade the linking theory, not the statistics — most are
  P1–P2 unless a formal semantics is defined and used (then P3).
- When torn between two grades, take the lower and say why in the rationale.
