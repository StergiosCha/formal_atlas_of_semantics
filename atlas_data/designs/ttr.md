# Design: `atlas/ttr/TTR.v` — Type Theory with Records (Cooper)

> **SOURCE UPDATE 2026-09-05**: Cooper 2023 is now ON DISK at `papers/foundations/Cooper_2023_FromPerceptionToCommunication.pdf` (also: the full Modern Perspectives 2017 volume). Resolve every [NOT-ON-DISK] tag against the PDF during the build session.


Target: `atlas/ttr/TTR.v` (create `atlas/ttr/`). Coq 8.20.1, stdlib only.
Style models: designs/inqb.md (judged decisions), designs/mtt_ranta.md
(comparison hooks). Compile with the standard repo command.

## Sources
- Cooper 2023, *From Perception to Communication* (OUP) — NOT on disk;
  cite by chapter [NOT-ON-DISK: spot-check when PDF added]. Core TTR
  formal appendix (records, record types, subtyping, meets) is the
  target.
- Cooper 2005, "Records and record types in semantic theory", J. Logic &
  Computation 15 [NOT-ON-DISK].
- Cooper, Dobnik, Lappin & Larsson 2015 (on disk:
  papers/probabilistic/Cooper_Dobnik_Lappin_Larsson_2015_ProbabilisticTypeTheory.pdf)
  — §2 has a compact self-contained TTR core (judgements, record types,
  ptypes) usable for page-precise citations; §3-4 the probabilistic
  layer (STRETCH).
- Raw material: ttr_mtt/TTR_base.v, TTR_records.v, TTR_types.v,
  TTR_shallow.v, TTR_theorems_shallow.v, TTR_theorems_deep.v — audited
  2026-09-05 (see records/ttr_mtt__*.json): shallow Coq-record
  encodings, Parameter-heavy, no subtyping theorems. Their content is
  redone under the zero-axiom discipline; keep their example inventory
  (Aristotle-style records, event examples).

## THE decision (judged): deep labelled records vs shallow Coq records

**Design A (shallow, the pilots)**: TTR record types as Coq records/
sigma-types. Pro: dependent fields free. Con: subtyping (width+depth),
relabelling, meets are NOT statable — Coq records are nominal and
generative; the pilots prove no structural theorem. This is precisely
what the audit found: the pilots have no subtyping content.

**Design B (deep, ADOPTED)**: labels as a decidable type (`Inductive
label := l_x | l_e | l_c | ... ` for the fragment, or `label := nat`
with notation); a base universe of types as an inductive `BType`
(individuals, ptypes over a signature, prop-like); record TYPES as
association lists `rty := list (label * ty)` with
`ty := TBase b | TRec rty` (nested); RECORDS as association lists of
values `rec := list (label * val)` with `val := VBase dom-element |
VRec rec`; the judgement `of_type : val -> ty -> Prop` and
`of_rty : rec -> rty -> Prop` by mutual recursion/induction (field
lookup: every label of the type is present in the record with a value
of the field's type — records may have MORE fields: width subtyping is
then a THEOREM shape, not a stipulation).
Dependent fields (the real TTR: later fields may depend on earlier
ones — ptypes with arguments referencing labels) are the hard part:
adopt the standard first-order compromise — ptype arguments are label
PATHS resolved against the record (`PArg := path`), so dependency is
by reference, not binding. This keeps everything first-order and
decidable and is exactly Cooper's official notation r.x. Document as
the file's central artifact.
Zero axioms: signature (individuals, predicates) as Section variables;
demos with concrete Inductives.

## MUST scope (~18 theorems)
1. Judgement basics: `of_rty` for empty type (everything of type []);
   field access `rec_get`; determinism-up-to-lookup.
2. Width subtyping `sub_w : rty -> rty -> Prop` (every field of the
   super occurs in the sub with the SAME type): reflexive, transitive,
   and SOUND: `sub_w T1 T2 -> of_rty r T1 -> of_rty r T2` (the TTR
   slogan "more fields = subtype", Cooper 2023 ch. 2 / CDLL15 §2).
3. Depth subtyping (recursive: field types may shrink) `sub_d`,
   soundness by mutual induction; combined `sub := sub_d` includes
   `sub_w`.
4. Decidability of `sub` on the fragment (labels decidable, types
   first-order): `subb : rty -> rty -> bool` with `subb_sound/complete`.
5. Meet of record types (field-wise union, recursive meet on shared
   labels when compatible): `meet T1 T2 = Some T` with
   `of_rty r T <-> of_rty r T1 /\ of_rty r T2` (the TTR meet theorem);
   None exactly on incompatible shared fields (documented).
6. Relabelling: a label bijection induces an equivalence on types and
   records preserving `of_rty`.
7. The worked examples redone from the pilots: the "a man runs" record
   type [x : Ind, c1 : man(x), c2 : run(x)] with a witness record;
   judgement theorems; the subtype chain [x, c1, c2] <= [x, c1] <= [x].
8. Comparison hooks (for a future TTR↔MTT edge): the man-record-type's
   witnesses correspond to MTT's {x : Entity | man x /\ run x} — state
   the two-way translation on the fragment (records-to-sigma), proving
   round-trip on witnesses. This is the TTR analogue of
   PTQ_vs_MTT's guarded-quantification bridge.

## STRETCH
Probabilistic TTR (CDLL15 §3: p(a : T) axioms on a finite model —
reuse RSA.v's QSum kit); string types for events (Cooper 2023 ch. 3);
function types and their subtyping (contravariance); situation types.

## Pitfalls
1. Association lists need NoDup labels: carry `wf_rty` (label
   uniqueness) as a side predicate; every theorem lists it explicitly.
2. Mutual recursion ty/rty and val/rec: define with nested `list`
   recursion (Coq's guard handles `list` via nested fixpoints or
   `Forall`-style predicates — prefer explicit Fixpoints over lists,
   with induction principles proved by hand: the standard nested-
   inductive dance; budget it).
3. Paths for dependency: resolution is partial — use `option` and make
   `of_rty` require successful resolution; the failure mode is a
   documented artifact (TTR's metatheory assumes well-formedness).
4. Decidable equality on labels: derive with `Scheme Equality` or a
   hand-rolled eqb + eqb_spec.
5. Keep the MTT-hook translation in a separate Section so DisCoCat-style
   phantom tricks aren't needed; witnesses translate by structural
   recursion.
6. Zero-axiom discipline per GUIDE.md; the pilots' Parameters become
   Section variables.

## Build order
1. labels + ty/rty + val/rec + wf predicates; compile.
2. of_type/of_rty + basic judgement theorems (block 1, 7's examples as
   smoke test); compile.
3. sub_w + soundness; sub_d + soundness; compile.
4. subb decidability; compile.
5. meet + the iff theorem; compile.
6. relabelling; compile.
7. MTT hooks (block 8); audit block (Print Assumptions, expect all
   closed); records + edge JSON (ttr__mtt) after.
Estimated 700-1000 lines.
