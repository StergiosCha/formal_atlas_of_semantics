# P0/P1/P2 coverage campaign — frozen prospective protocol

2026-09-13. Selection approved by the user before source reading in this
campaign. This is a purposive, single-researcher case study, not random or
blinded sampling. Prior general familiarity with the authors is not excluded.
Do not replace a source after seeing its difficulty or its proof results.

| ID | Frozen tier | Selected source | PDF SHA-256 |
|---|---|---|---|
| 172 | P0 | Derrida 1972, Signature Event Context | 74b4e049de0c17bc93cfb847883818eb0a54d712660e44f63d5ca698c83fdd2a |
| 177 | P1 | Austin 1962, How to Do Things with Words | c01dfdf21bfbdcc19bdf4ea7092f88795a85ac9eea04627e86bc24a5277f1dc5 |
| 67 | P2 | Horn 1984, Toward a New Taxonomy for Pragmatic Inference | 6e03564d933b570c7b23af201de1004e069df6ee7c4ff4c913b42fb852f8cfaa |

Baseline atlas SHA-256:
`713a450798fe463ccc41c5db4a05c918a8d7c93ea72bddf91f1f1ecfd9801fb0`.
Frozen formality.json SHA-256:
`35dc302ae28c91e7e7d4c9677713b35bbd6af014ccb3aef6253e126f59eead0e`.
Baseline: P0 has no Coq contact; P1 and P2 have one pilot each, no F4/F5.

## Fixed scope and sequence

Read and inventory the source before designing its encoding. Inventory
ontology, definitions, claims and non-formal remainder with printed pages.

- Derrida: iterability, repeatable marks, separation from original context,
  and limits on what this licenses concerning meaning. Read the whole essay;
  retain the Austin/signature discussion in the scope audit even if it has
  no suitable mathematical statement. Do not equate iterability with identical
  meaning, arbitrary successful reuse, or a theorem about every context.
- Austin: conventional procedures, felicity conditions, misfires and abuses,
  with source examples. Start with the lectures introducing/developing that
  taxonomy, not a claim to formalize the whole book or all speech acts.
- Horn: Q/R principles and the source's contrasting inference patterns.
  Identify prerequisites, exceptions, cancellation and competition rather
  than treating every conversational inference as an unconditional entailment.

For each: attempt a bounded implementation with a source-motivated positive
case and a boundary/countercase. Generalize only where the source warrants it.
If central notions require reconstruction, preserve that distinction in the
Coq header, definition mappings, and results. A mathematical model illustrating
a reading is not a proof of the original philosophical or empirical claim.

## Fixed evaluation criteria

Record for every selected claim: direct source formalization, conditional
result with named premises, illustrative reconstruction, refutation, not
statable in this signature, or unfinished engineering. Match definitions as
exact/simplified/changed/added/missing under RUBRIC.md. Distinguish the source's
own qualifications from assumptions added by the implementation.

Check compilation, Print Assumptions, kernel checking, positive and negative
examples, and triviality/vacuity probes. No axioms or admissions may be used to
make the planned examples pass. A supplied premise is not an inferred result;
a definitional checklist is not empirical validation.

A bounded attempt is complete when every inventoried target has an explicit
disposition and the implemented cases pass their checks. This does not by
itself establish a completed formalization of the whole source. Withhold a
theory-level determination if the central scope remains uncovered or the
mechanism is an added reconstruction. Independent source review remains
pending; do not represent a self-review as a second independent reviewer.

Preserve all 230 intrinsic grades and original survey inputs. Add evidence
links separately. No estimate of a formality gradient or resistance rate from
these three cases. Keep results separate; do not revise this protocol after
reading the sources. TTR/MTT/Ranta/DTS expansion is paused for this campaign.
