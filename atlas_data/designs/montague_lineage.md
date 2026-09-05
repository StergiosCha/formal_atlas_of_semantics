# Design: `atlas/montague/` — the Montague lineage (PTQ trunk + graded edges)

User proposal 2026-09-05: the original Montague as a trunk, with edges showing
how the things called "Montague(-style)" build on or diverge from PTQ, each
edge graded by the comparison methodology (edges/*.json, grades 0–5,
similarity + overlap computed by consolidate.py).

Files (this batch):
- `atlas/montague/PTQ.v` — the trunk. Montague 1973 (PTQ), extensional core +
  intensional layer, zero axioms (Section-quantified domains; the existing
  `shallow/PTQ.v` is richer but Parameter/Axiom-based and stays as raw
  material).
- `atlas/montague/PTQ_vs_Lambek.v` — edge to atlas/type_logical/Lambek.v
  (Curry–Howard categorial grammar computes Montague meanings).
- `atlas/montague/PTQ_vs_MTT.v` — edge to atlas/mtt_ranta/MTT.v (CNs as
  predicates vs CNs as types; guarded quantification = subset-type
  quantification).
- Edge JSONs: `edges/ptq__lambek.json`, `edges/ptq__mtt.json`,
  `edges/ptq__kratzer.json` (evidence: shallow/kratzer2.v's
  kratzer_equals_montague + empty_base_characterization),
  `edges/ptq__barwise_cooper.json` (evidence: PTQ.v's conservativity/
  monotonicity theorems + extras/BarwiseCooper.v).
Later (queued): PTQ↔DPL (dynamic turn), PTQ↔Heim/FCS, PTQ↔DisCoCat.

## PTQ.v scope (MUST)
1. IL types shallowly: e = Entity (Variable), t = Prop, <a,b> = A -> B,
   <s,a> = Index -> A with Index a Variable; intension/extension operators.
   (PTQ p. 256ff; the Time component of Montague's <A,I,J,<=,F> is folded
   into Index — artifact note.)
2. NPs as generalized quantifiers (extensionalized): NP := (Entity -> Prop)
   -> Prop; john* = fun P => P john (type raising, PTQ T2); every/a/no as
   determiners; "every man walks", "a man walks" with their meanings.
3. Quantifying-in (PTQ T14) as the scope mechanism: "every man loves a
   woman" surface (∀∃) and inverse (∃∀) readings; theorem: inverse entails
   surface; countermodel-free (schema: exists-forall -> forall-exists).
4. Intensional transitive verbs: seek : Entity -> ((Entity->Prop) -> Prop)
   -> Prop rendered de dicto; find as the extensional lift of a first-order
   relation with the PTQ meaning postulate shape; theorems:
   - find_dedicto_dere: "John finds a unicorn" <-> exists u, unicorn u /\
     find0 john u (the meaning postulate for extensional verbs, PTQ MP);
   - seek_no_existence: there is a seek-relation and a model where "John
     seeks a unicorn" (de dicto) holds and no unicorn exists (existence
     countermodel, axiom-free) — the PTQ headline;
   - dere_existence: the de re reading entails existence.
5. B&C hooks: PTQ's determiners are conservative and right-monotone
   (theorems every_conservative, a_conservative, no_conservative,
   every_mon_down/up etc.) — the evidence base for edges/ptq__barwise_cooper.
6. Modal/tense layer, minimal: box phi := forall i, phi i over Index;
   necessarily-validities (K, Nec) — the evidence hook for ptq__kratzer
   (kratzer2.v proves kratzer_must (empty background) = box).

## Edge files
- PTQ_vs_Lambek.v: Require type_logical.Lambek + montague.PTQ. Theorems:
  Lambek's Fragment.every_man_walks_sem RHS IS PTQ's every-man-walks meaning
  (compose the two equations; grade 5 on quantified sentences); same for
  some/john/type-raising (Fragment.type_raise_sem vs PTQ john* — literally
  fun P => P john both sides).
- PTQ_vs_MTT.v: Require mtt_ranta.MTT + montague.PTQ. Theorems: for a domain
  Entity and man : Entity -> Prop, MTT-quantification over the subset-CN
  {x | man x} is PTQ's guarded quantification (both directions; grade 4);
  some-side likewise; divergences prose: selection restrictions/subtyping
  not statable in PTQ, single sorted domain not statable in MTT (its CNs
  are many types).

## Rules
Zero axioms in all new files; compile after each file with the standard
command; records for each .v; edge JSONs graded from the actual theorems;
consolidate + build_site at the end.
