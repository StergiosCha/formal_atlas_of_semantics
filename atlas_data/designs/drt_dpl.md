# Design: `atlas/dynamic/DRT_DPL.v` — DRT and the DPL equivalence

Target: `atlas/dynamic/DRT_DPL.v`. Coq 8.20.1. REUSES the committed
`atlas/dynamic/DPL.v` (Require dynamic.DPL): its models <D,F> with D
inhabited, total assignments, update g[x:=d], the relation semantics
`sem`, truth, and the donkey sentences dk1/dk2/dk3 with their proved
truth conditions. Do NOT redefine any of these — the bridge's value is
that the two sides share one model theory.

## Sources (on disk)
- Kamp, van Genabith & Reyle 2011 handbook chapter
  (papers/dynamic/Kamp_vanGenabith_Reyle_2011_DRT.pdf): DRS syntax
  (universe + conditions, complex conditions via negation, implication,
  disjunction), the verification/embedding semantics (an embedding
  function extends the input function on the universe and verifies all
  conditions), accessibility. Cite the chapter's numbered definitions
  after pdftotext spot-checks.
- Muskens 1996 (papers/dynamic/Muskens_1996_CombiningMontagueDRT.pdf):
  the DRS-as-relation view (§ on boxes: [u1..un | γ1..γm] as a binary
  relation on states) — the file's semantics IS Muskens' relational
  reading, which makes the DPL correspondence near-definitional.
- Groenendijk & Stokhof 1991 preprint § on DRT: their own sketch of the
  translation; the file's tr follows it.

## Definitions
- D1 `drs := mkDRS { universe : list Var; conds : list cond }` with
  `cond := c_atom (pred, list term) | c_eq term term | c_neg drs |
  c_imp drs drs | c_or drs drs` — mutual inductive (drs/cond via
  nested lists: define as mutual Inductive with explicit list
  recursion, or single inductive with `list cond` and hand-rolled
  induction principle — the DPL.v style favors the latter).
- D2 Verification, relationally (Muskens' reading of KvGR's embedding
  semantics): `verifies M (f g : assignment) (K : drs) : Prop :=
  extends_on (universe K) f g /\ Forall (csat M g) (conds K)` where
  `extends_on xs f g := (forall x, ~In x xs -> g x = f x)` (g differs
  from f at most on the universe — REUSE DPL.v's k[x̄]g machinery:
  its agreement-outside-a-set predicate) and `csat` interprets
  conditions (c_neg K := no h verifies K from g; c_imp K1 K2 := every
  verifying h of K1 extends to some verifying k of K2; c_or := some).
- D3 The translation `tr : drs -> form` (G&S sketch / standard):
  `tr (mkDRS [u1..un] [γ1..γm]) := ∃u1...∃un (tr_c γ1 ∧ ... ∧ tr_c γm)`
  with `tr_c (c_neg K) := ¬ tr K`, `tr_c (c_imp K1 K2) := tr K1 → tr K2`
  (DPL's dynamic →), `tr_c (c_or K1 K2) := tr K1 ∨ tr K2`, atoms/eq
  direct. Fold ∃ and ∧ right-nested over the lists.
- D4 Accessibility as a derived notion (subordination) — definitions
  only, one worked lemma (an antecedent in a c_imp's left box is
  accessible from the right box), not a full theory.
- D5 The donkey DRSs: K_dk2 := if [x,y | farmer x, donkey y, own x y]
  then [ | beat x y] as a drs; likewise the relative-clause version.

## MUST theorems (~14)
- T1 verification respects assignment agreement outside the universe.
- T2-T3 basic algebra: merging universes; empty-universe DRSs are
  tests (verifies iff conds hold and f = g on everything — matches
  DPL.v's `test` notion; cite its Def. 11 infrastructure).
- T4 THE HEADLINE, by mutual induction on drs/cond:
  `verifies M f g K <-> sem M (tr K) f g`
  (f verifies K yielding g iff (f,g) ∈ [[tr K]] in DPL). The ∃-fold on
  the universe corresponds to DPL's rex chain; conds-Forall to rcomp of
  tests; c_neg to rneg; c_imp to rimpl; c_or to rdisj. Expect the
  classical steps to mirror DPL.v's: the file may inherit `classic`
  exactly where DPL.v's d1-d3/d18/d20 use it (document per-theorem;
  groups as in DPL.v's audit).
- T5 truth transfer: `true_in M f K <-> truth M f (tr K)` (corollary).
- T6 the donkey corollary: `tr K_dk2` is DPL's dk2 up to provable
  equivalence, hence K_dk2's truth conditions are dk2_truth's ∀∀
  first-order formula — DRT's donkey inherits DPL.v's committed
  theorem. This is the atlas's DRT≈DPL edge content; write
  edges/drt__dpl.json from it (grades: semantics 4-5; syntax 1
  (re-encoding: boxes vs formulas); accessibility b-only).
- T7 (converse direction, cheap fragment) `dpl_to_drs` for the ∃/∧/¬
  fragment with the round-trip lemma on that fragment.

## STRETCH
Proportional/duplex conditions (out — no uniform semantics in the
chapter); DRS merge as an operation with tr-homomorphism; Muskens' CDRT
types.

## Pitfalls
1. Mutual induction principles for drs/cond with list nesting: generate
   with `Scheme`/`Combined Scheme` or hand-roll; T4's induction is the
   file's spine — get the principle right FIRST (smoke-test with a
   trivial mutual lemma).
2. Reuse, don't redefine: DPL.v's `sem` orientation is "h = g"-styled;
   match verification's direction to it or T4 will need flips
   everywhere. Read DPL.v Part 4 before writing D2.
3. The ∃-fold: prove a lemma `sem M (fold_ex xs φ) f g <-> exists-chain`
   once, generic over the list, before T4.
4. Classical usage: isolate; expected to match DPL.v's groups; zero
   NEW axioms beyond DPL.v's documented classic/funext profile.
5. Namespace: `Require dynamic.DPL` — qualify (DPL.form, DPL.sem);
   don't Import unqualified (name collisions with cond/test).

## Build order
1. drs/cond + induction principles + smoke lemma; compile.
2. verification D2 + T1-T3; compile.
3. tr D3 + fold_ex lemma; compile.
4. T4 by mutual induction (the long haul); compile per case if needed.
5. T5-T7 + donkey; audit; record + edges/drt__dpl.json; consolidate.
Estimated 600-900 lines.
