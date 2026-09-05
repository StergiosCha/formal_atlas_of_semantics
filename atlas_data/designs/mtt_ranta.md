# Design: `atlas/mtt_ranta/` — MTT-semantics (C&L 2020) and Type-Theoretical Grammar (Ranta 1995), as a comparable pair

Targets (three files, ONE region, this one design doc; user decision 2026-09-05:
"on a par, very close, should be able to compare them"):

- `atlas/mtt_ranta/MTT.v` — Chatzikyriakidis & Luo 2020, *Formal Semantics in Modern Type Theories*.
- `atlas/mtt_ranta/Ranta.v` — Ranta 1995, *Type-Theoretical Grammar*.
- `atlas/mtt_ranta/MTT_vs_Ranta.v` — the bridge (imports both; logical paths `mtt_ranta.MTT`, `mtt_ranta.Ranta` under `-R atlas ""`).

Coq 8.20.1, stdlib only. Compile from the repo root:
`coqc -R shallow "" -R deep "" -R extras "" -R ttr_mtt "" -R atlas "" atlas/mtt_ranta/<File>.v`
(bridge last; it Requires the other two, so they must be compiled first).
Style model: `atlas/type_logical/Lambek.v` and `atlas/inquisitive/InqB.v` (header,
per-theorem source refs, artifact classes, `Print Assumptions` audit, zero `Admitted`).

## Sources

- **CL20** = Chatzikyriakidis & Luo 2020, `papers/foundations/Chatzikyriakidis_Luo_2020_FormalSemanticsInMTT.pdf` (searchable). Chapters: 2 (MTTs), 3 (CNs-as-types, subtyping, adjectives), 4 (advanced modification), 5 (copredication/individuation), 6 (Coq), 7 (advanced), App. 6 (dot-type rules), App. 7 (their own Coq code — cross-check, do not copy uncritically).
- **R95** = Ranta 1995, the djvu in the folder root (`djvutxt -page=N` works; djvu page ≈ printed page + ~12; cite by SECTION). Chapters: 2 (gradual TT: §2.11 substantival/adjectival terms, §2.12 separated subsets, §2.16 props-as-types, §2.18–2.21 quantifiers), 3 (logical operators in English: §3.1 quantifiers, §3.4–3.5 sugarings of Σ and Π, §3.8–3.9 disjunction/negation), 4 (anaphora: §4.2 pronominalization, §4.13 discourse referents), 6 (text: §6.1 progressive conjunction, §6.2 text as context), 9 (sugaring and parsing; Appendix: sugaring in ALF).
- Satellite (spot-checks only): Luo 2012 CNs-as-types; C&L 2013 adjectives; C&L 2014 NLI in Coq (all in `papers/foundations/`).
- The `ttr_mtt/` pilot files (`Coq_book_ontology.v`, `Book_*.v`) are RAW MATERIAL: their renderings are broadly right but their `Parameter`/`Axiom`+`Coercion` style contaminates every audit. The atlas files re-do the content under the zero-axiom discipline below and the record notes what was inherited.

## Judgment / decisions (do not re-litigate)

1. **Zero axioms, zero global Parameters.** Everything is either (a) a general
   schema, ∀-closed over Section Variables (types, predicates, individuals), or
   (b) a concrete demo built from Inductives/Definitions. `Print Assumptions`
   on every headline theorem must print "Closed under the global context".
   This is the single biggest departure from the pilots and from CL20's own
   App. 7 code, and it is what makes the pair auditable.
2. **`CN := Type`** (not `Set`), following CL20's universe `CN` (§3.2.1); a
   `Definition CN := Type.` in each file (kept definitionally transparent).
3. **Coercive subtyping = explicit lifting functions + `Local Coercion`.**
   Global `Coercion` on section variables does not survive `End Section`;
   subtyping theorems are stated with the lifting explicit
   (`walk (mh x)`), and the coercion sugar is demonstrated inside the
   section where it is legal. Artifact class (iv): Coq coercions are the
   implementation, CL20's `≤c` is the spec; no `Axiom` coercions ever.
4. **Dot-types as two-projection records**: `Record PhyInfo := { phy :> Phy;
   info :> Info }` over section variables `Phy Info : CN` (CL20 §5.2, App. 6;
   the pilots' rendering, kept). Documented as an ENCODING of Luo's dot-types
   (no native support; the record has pairing where dot-types forbid it —
   record the mismatch, artifact class (ii)).
5. **Ranta's fragment carries the deep embedding, MTT.v carries none.**
   Sugaring (R95 ch. 9) needs syntax to recurse on; so Ranta.v deep-embeds a
   SMALL phrase grammar (categories S/CN/NP/VP, ~10 constructors), gives it
   (i) a type-valued semantics and (ii) a linearization to word lists, and
   proves the example sentences' semantics and strings match R95's. MTT.v
   stays shallow throughout (CL20 work directly in the type theory).
   `word` is a small Inductive enumeration; NO `String` library.
6. **Both files parameterize over the SAME abstract lexicon shape** —
   `Section`s with `Variables (Farmer Donkey Man : CN) (own beat : ...)`
   etc., names agreed here — so the bridge can apply both files'
   section-lifted constants to the same variables and state agreement,
   ideally by `reflexivity`.
7. **Prop vs Type**: Ranta.v interprets propositions as `Type`
   (props-as-types, R95 §2.16); MTT.v uses `Prop` (UTT's impredicative
   `Prop`, CL20 §2.3.1). The bridge states the agreements up to the
   inclusion `Prop ⊆ Type` where needed; where impredicativity or
   proof-irrelevance would matter it is prose in the header, not a theorem.
8. **DPL connection is STRETCH.** The bridge proves the Π/Σ ↔ ∀∀ currying iso
   (Ranta's strong donkey reading) as MUST; instantiating DPL's relational
   models to compare with `dynamic.DPL`'s `dk2_truth` is STRETCH (B7).
9. NEXT.md cost rules stand: no subagents, no workflows, compile after every
   step, zero `Admitted` at every checkpoint, one FILE per session (three
   sessions + this design), record per file afterwards.

## 1. Scope

### MTT.v — MUST
1. Basic categories (CL20 §3.1): CNs as types in the universe `CN`; IVs as
   `A -> Prop`; TVs as `A -> B -> Prop`; adjectives as predicates; sentence
   meanings as `Prop`. Quantifiers `some/all/no/a` polymorphic over `CN`.
2. Subtyping (CL20 §3.2.2): lifting functions as the rendering of `≤c`;
   monotonicity schemata: if `Man ≤ Human` then `all Human P -> all Man
   (P ∘ mh)` and `some Man (P ∘ mh) -> some Human P`; composition and
   contravariance for function types (CL20 §2.4).
3. Judgmental interpretations and their propositional forms (CL20 §3.2.3,
   §7.1): `John : Man` vs the proposition `exists x : Man, x = john`; the
   `is_a` predicate via lifting.
4. Adjectival modification, the CL20 §3.3 case study, one theorem block per
   class:
   - intersective (§3.3.1): `AdjCN A P := {x : A | P x}` (Σ/sig); inferences
     Σ→noun and Σ→adjective; "black man is a man".
   - subsective (§3.3.2): `skilful : forall A : CN, A -> Prop`; "skilful
     surgeon is a surgeon" (typing); NON-inference "skilful surgeon ->
     skilful man" documented (no theorem; countermodel over a 2-element
     lexicon: skilful as surgeon but not as man).
   - privative (§3.3.3): `Gun := RealGun + FakeGun` (sum); `fake gun` is a
     gun in the extended sense, and provably not a real gun; the CL20
     coercion picture over the sum.
   - non-committal (§3.3.4): `alleged : (A -> Prop) -> (A -> Prop)` opaque —
     no veridicality theorem; document the deliberate absence.
5. Adverbs (CL20 §4.5.1–4.5.2): veridical manner adverbs via the subset
   type: `quickly : forall A (V : A -> Prop), {v : A -> Prop | forall x,
   v x -> V x}`-style; theorem `walk_quickly x -> walk x`.
6. Copredication with dot-types (CL20 §5.2, App. 6): `PhyInfo` record with
   both projections coercions; `Book := Σ`-over-PhyInfo or a section
   variable `Book : CN` with a lifting to `PhyInfo`; "John picked up and
   mastered the book" typechecks and entails each conjunct.
7. Individuation (CL20 §5.3, MUST-lite): CNs as setoids `(A, eq_A)`;
   counting "three books" relative to the setoid; theorem that phy- and
   info-individuation give different counts on an explicit 2-copy/1-content
   toy lexicon. (Full generic numerical quantifiers of §5.3.2: STRETCH.)
8. An NLI mini-suite (CL20 ch. 6 spirit, C&L 2014): ~8 entailments as
   theorems over the abstract lexicon (quantifier monotonicity, adjective
   drops, conjunction/disjunction, copredication inferences).

### MTT.v — STRETCH
Gradable adjectives with degrees (§4.2–4.3); multidimensional adjectives
(§4.4); generic numerical quantifiers (§5.3.2); dependent event types (§7.2);
intensional adverbs (§4.5.4).

### Ranta.v — MUST
1. Props-as-types logic kit (R95 §2.16–2.21): `every A B := forall x : A, B x`
   (Π), `some A B := {x : A & B x}` (Σ), disjunction as sum, negation as
   `-> Empty`, all at `Type`; separated subsets `{x : A & B x}` for
   substantival modification (§2.11–2.12) — "a man who owns a donkey".
2. Quantifier sentences (§3.1, §3.5): "every man walks", "some man walks",
   "no man walks" with their Π/Σ interpretations; the ordering principle for
   nested quantifiers (§3.2): "every man owns a donkey" as Π-over-Σ.
3. The donkey sentences (§3.2, §4.2): "if a farmer owns a donkey, he beats
   it" as `forall z : {x : Farmer & {y : Donkey & own x y}}, beat (pi1 z)
   (pi1 (pi2 z))`; pronouns as projections (§4.2 pronominalization rule);
   THE theorem: the currying iso with the ∀∀-form (strong reading),
   constructive, both directions.
4. Text as progressive conjunction (§6.1–6.2): two-sentence discourse
   "A man walks. He talks." as `{p : {x : Man & walk x} & talk (pi1 p)}`;
   contexts as nested Σ (telescopes); theorem: discourse extension =
   Σ-associativity iso `{p : {x:A & B x} & C (pi1 p)} ≃ {x:A & {b : B x &
   C x}}` (the workhorse for R95's context manipulation).
5. The deep fragment + sugaring (R95 §1.7, ch. 9): Inductive categories and
   trees for the fragment {every/some/a + CN, CN with relative clause, VP
   with TV + NP or IV, conditional donkey}; `denote : tree -> Type`
   (shallow semantics), `linear : tree -> list word`;
   theorems: the donkey tree linearizes to
   `if a farmer owns a donkey , he beats it` and denotes the Π-over-Σ type
   above (by `reflexivity`/`vm_compute`); same for 3–4 more R95 example
   sentences. Sugaring is TT→NL (R95's direction); parsing: STRETCH.

### Ranta.v — STRETCH
Parsing as inverse of sugaring on the fragment (ch. 9.7, with a
correctness/roundtrip theorem); definite phrases and the genitive (§4.3–4.5);
temporal reference (ch. 5); propositional questions (§6.11); belief contexts
(ch. 7); higher-level type theory (ch. 8).

### MTT_vs_Ranta.v (bridge) — MUST
- B1 CN agreement: both files' `CN` is `Type` and CN meanings coincide —
  by `reflexivity` after applying both to the shared lexicon.
- B2 Quantifier agreement: `MTT.all = Ranta.every`-style equations at
  `Prop`/`Type`; where MTT uses `exists`(Prop) and Ranta `{_ & _}`(Type),
  the bridge proves the two-way implication `Ranta.some A B -> MTT.some A
  (fun x => inhabited-of B)` and back under `inhabited`; the design accepts
  `inhabited`/truncation as the honest mediator (artifact class v).
- B3 Intersective adjectives = separated subsets: CL20 §3.3.1's Σ IS R95
  §2.12's subset — definitional agreement theorem.
- B4 Donkey agreement: MTT.v's donkey rendering (CL20 follow Ranta) equals
  Ranta.v's up to the Prop/Type mediation of B2; plus the shared currying
  iso re-exported.
- B5 Subtyping divergence: the fragment sentence needing `Man ≤ Human`
  typechecks in MTT.v with the lifting and has NO Ranta.v counterpart
  without manual insertion — documented with a commented `Fail Check` and
  a theorem that the manually-lifted forms agree.
- B6 Sugaring divergence: prose + the observation (theorem-free) that
  MTT.v has no `linear`; Ranta's `linear` applied to the shared fragment.

### Bridge — STRETCH
- B7 vs DPL: instantiate `dynamic.DPL`'s model with a type-theoretic domain
  and prove Ranta's ∀∀ donkey form coincides with `dk2_truth`'s first-order
  truth condition (classically equivalent; constructively the Σ-form is
  stronger — state the one provable direction constructively).

### Deliberately out (all three files)
First-order-logic completeness questions; R95 chs. 5, 7, 8, 10 (temporal,
belief, higher-level TT, morphology-level structures); CL20 ch. 7.3
(dependent categorial grammars — overlaps Lambek.v's territory, note only);
GF and any parsing beyond the fragment; TTR (own queue item).

## 2. Representation decisions

| Notion | Coq | Justification |
|---|---|---|
| Universe of CNs | `Definition CN := Type` | CL20 §3.2.1 universe CN; R95 works in "sets"; Type avoids Set-universe traps. |
| Lexicon | Section `Variables`, shared NAMES across files: `Man Woman Human Farmer Donkey Surgeon Phy Info : CN`; `john : Man`; `walk talk : Human -> Prop`; `own beat : Farmer -> Donkey -> Prop`; `mh : Man -> Human` etc. | Zero-axiom discipline (decision 1); bridge applies both files to one shared set (decision 6). |
| Subtyping | explicit lifts + `Local Coercion` in-section | decision 3; CL20 §2.4, §3.2.2. |
| Intersective Adj / subset CN | `{x : A & P x}` (`sigT`; `sig` when P : Prop in MTT.v) | CL20 §3.3.1; R95 §2.12. Bridge B3. |
| Subsective Adj | `forall A : CN, A -> Prop` applied per-CN | CL20 §3.3.2. |
| Privative | sum type `Real + Fake` | CL20 §3.3.3's extension picture. |
| Dot-type | 2-projection record, both projections `:>` | CL20 §5.2, App. 6; pilots' rendering; encoding gap recorded. |
| Setoid CN | pair `(A, R : A -> A -> Prop)` + equivalence hypotheses | CL20 §5.3; no stdlib Setoid class dependence in statements. |
| Ranta propositions | `Type`; Σ = `sigT`, ∨ = `sum`, ¬ = `-> Empty_set` | R95 §2.16–2.21 (decision 7). |
| Pronouns | projections `pi1`/`pi2` out of context Σs | R95 §4.2. |
| Text/context | nested `sigT` (telescopes) | R95 §6.1–6.2. |
| Fragment syntax | small Inductives `cat`, `tree : cat -> Type` over an Inductive `word` | decision 5; R95 ch. 9 needs syntax; `denote`/`linear` Fixpoints. |
| Bridge mediation Prop/Type | `inhabited` where universes differ | B2; the honest cost of CL20-Prop vs R95-Type (artifact v). |

## 3. Pitfalls

1. The pilots' `Axiom`+`Coercion` pattern is BANNED — it silently poisons
   `Print Assumptions` of everything downstream. Grep the finished files for
   `Axiom|Parameter` before the audit; expected count: zero.
2. `Coercion` on a section variable is local to the section; do not expect
   post-section sugar. State theorems with explicit lifts.
3. Records with `:>` projections over section variables: check after `End`
   that the coercions survive parameterization (they do, but the target
   classes change — `Check` the copredication sentence again post-section).
4. `sigT` vs `sig` vs `ex`: keep MTT.v in `Prop` (`sig`/`ex`) and Ranta.v in
   `Type` (`sigT`/`sum`); NEVER mix within a file, or the bridge equations
   stop being definitional. The bridge alone mentions `inhabited`.
5. In the currying iso and Σ-associativity, avoid `destruct` on `sigT` in
   `Prop`-valued goals going the wrong way; both isos are plain `fun`-term
   constructions — write the terms.
6. The fragment `denote` is dependently typed (`tree c -> interp c`);
   define `interp : cat -> Type` FIRST and keep constructors non-indexed
   otherwise; `simpl`/`vm_compute` on `linear` needs `word` concrete —
   hence the Inductive enumeration, no abstract alphabet.
7. Universe pitfalls: `CN := Type` means records/sums over CNs live one
   level up; if a universe inconsistency appears, do NOT add
   `Set Universe Polymorphism` globally — localize the offending
   definition; record any residue in the header.
8. CL20's App. 7 Coq code is a convenience transcript, not the spec —
   formalize from the chapters; where App. 7 and the text disagree, follow
   the text and note it (candidate `source_gap` entries).
9. Keep every theorem's source ref at SECTION granularity (both books'
   printed page numbers differ from PDF/djvu pagination; R95: djvu ≈
   printed + ~12; CL20 PDF is searchable).
10. Bridge imports: `Require Import mtt_ranta.MTT mtt_ranta.Ranta.` — name
    collisions (`some`, `all`, `every`) are CERTAIN; qualify everywhere in
    the bridge (`MTT.some`, `Ranta.some`); do not `Import` both unqualified.

## 4. Build order

Session A (MTT.v): 1. header+CN+lexicon section; 2. quantifiers+subtyping
schemata; 3. judgmental/propositional forms; 4. adjectives (four classes);
5. adverbs; 6. dot-types/copredication; 7. individuation-lite; 8. NLI suite;
9. audit block. Compile after every step; `Print Assumptions` at 2, 4, 6, 9.

Session B (Ranta.v): 1. header+Type-logic kit; 2. quantifier sentences +
ordering; 3. donkey + currying iso; 4. text/telescopes + Σ-assoc iso;
5. fragment syntax + denote; 6. linear + sugaring theorems; 7. audit block.

Session C (bridge): B1–B6 in order, then STRETCH B7 only if budget remains;
audit block; then the pair's records (`atlas__mtt.json`, `atlas__ranta.json`,
`atlas__mtt_vs_ranta.json` — or one `atlas__mtt_ranta.json` per region
convention if consolidate.py prefers; check `consolidate.py` first),
consolidate + build_site.

Headline audit lists (all expected "Closed under the global context"):
- MTT.v: quantifier monotonicity pair, intersective inferences, privative
  non-gun theorem, adverb veridicality, copredication entailments,
  individuation count theorem, the NLI suite.
- Ranta.v: donkey currying iso, Σ-associativity, the sugaring equations
  (donkey linearization + denotation), pronominalization examples.
- Bridge: B1–B4 agreement theorems.
