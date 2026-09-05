# Design: `atlas/dynamic/DPL.v` — Groenendijk & Stokhof (1991), *Dynamic Predicate Logic*

**Panel verdict.** Design B's *semantics-first* architecture is adopted as the skeleton: Def. 2 is factored through eight relation operators (`rtest`, `rcomp`, `rneg`, `rdisj`, `rimpl`, `rex`, `rall`, `rclos`) and `sem` is defined *literally* by them, so every unconditional §3.4 law is proved once for arbitrary relations and instantiated to formulas by `simpl`; this also gives the closure operator ♦ (Def. 17) an honest home without adding it to the syntax. Design A's stronger *coverage* and *concretes* are grafted in: numbered Facts 8, 13–16 as MUST (not STRETCH) via one transfer lemma; the D1–D50 numbering of the §3.4 displays (checked against the typescript pp. 20–25 / journal pp. 61–66, order identical); its signature record with `Var := nat`; its `Σ_ex`/`M_bool` and `Σ_dk` countermodel/donkey modules quantified over an arbitrary domain; and its `fact6_refuted` theorem. Two representation disputes are settled definitively: (1) **functional extensionality is imported globally** — the source's assignments are set-theoretic functions, hence extensional, and both designs' funext-avoidance schemes fail on the same lemma (A's `transfer_pw` is *false* without funext in the test cases, where the output must be Leibniz-equal to the input; B then needs funext for D32/D33/D47 anyway). Axiom use is audited per theorem, and the headline items (Egli, associativity, the ¬¬ countermodel, both donkey theorems, Fact 9) are proved axiom-free. (2) The transfer lemma takes B's *existential* form (output produced, pointwise-characterised), which is the form that survives induction; A's given-output form is derived from it with funext.

A 200-line judge probe (`scratchpad/dplprobe/DPLProbe.v`, Coq 8.20.1, stdlib only) compiled the layered `sem`, the `dpl_scope` notations, Fact 9, Egli's theorem/corollary, associativity, the `¬¬∃xPx ≢ ∃xPx` countermodel in witness form, and both donkey truth conditions over an arbitrary domain, all three `Print Assumptions` reporting "Closed under the global context". Pitfalls §6 records what the probe had to fix.

Source spot-checks by the judge (typescript T / journal P): Def. 1–2 (T 13–14, P 53–54); Def. 3–12, Facts 1–6 (T 15–17, P 55–58) — Def. 12 omits ∀ in *both* editions while the preceding sentence lists universally quantified formulas among the tests; Def. 13–16, Facts 7–9 (T 18–19, P 58–61); §3.4 displays (T 20–25, P 61–66) — the typescript prints the idempotency non-law as `φ ≄ ψ ∧ φ` (typo), the journal (P 63) as `φ ≄ φ ∧ φ`, and the prose ("counterexample against idempotency") settles it; Def. 17 (T 22, P 63); Def. 18–22, Facts 10–16 (T 25–29, P 66–70) — the printed proof of Fact 16 swaps `AQV(ψ) ∩ FV(χ)` to `AQV(χ) ∩ FV(ψ)` in one line; the Fact's statement is the correct one; (1b)/(2a)/(2b)/(3b) (P 41–42, T 2–3); Dekker 2012 §2.1 Def. 1 and Observations 1–2 (Egli's Theorem/Corollary) agree with Def. 2 clauses 1, 3, 4, 7 and with D46/D48.

Numbering used in the file: `Fact n` = the source's numbered Facts 1–16 of §3; `Dk` (k = 1..50) = the unnumbered displayed laws of §3.4 in reading order (table in §4.4 below); every Coq theorem carries a comment of the form `(* G&S 1991 §3.4 P 65 / T 24, D46: ∃xφ ∧ ψ ≃ ∃x[φ ∧ ψ]  (= Dekker 2012 Obs. 1, Egli's Theorem) *)`.

---

## 1. Scope

### MUST
- **Syntax** (Def. 1): terms (variables, constants), atoms `R t1…tn` with predicates of arbitrary arity, identity, and *all eight* connectives ¬ ∧ ∨ → ∃x ∀x as primitive constructors; their interdefinability (D1–D3) is a theorem.
- **Models** ⟨D, F⟩ with D non-empty (arbitrary Coq `Type`, no finiteness, no decidable equality on D); total assignments `Var → D`; ⟦t⟧_g; `k[x]g`.
- **Semantics** ⟦φ⟧ ⊆ G × G, Def. 2 clauses 1–8 verbatim (including the source's `h = g & … h …` orientation in the test clauses), via the relation layer; ♦ (Def. 17) as a relation operator and as the syntactic surrogate `¬¬` at formula level.
- **Semantic notions** Def. 3–12: truth, validity, contradiction, satisfaction set, s-equivalence, equivalence, production set, p-equivalence, test, condition (with ∀ added to Def. 12 and the omission flagged).
- **Static/dynamic distinction**: atoms, identity, ¬, ∨, →, ∀, ♦ are tests; ∧ of tests is a test; ∃xPx is not a test (countermodel).
- **Binding at variable level**: `AQV`, `FV` (Def. 15–16, computed structurally from the variable-level content of Def. 13); Fact 9; the transfer lemma; Fact 8.
- **Numbered Facts** 1, 2, 3, 4, 5, 6 (⇐ direction proved; ⇒ refuted by a theorem), 8, 9, 10, 11, 12, 13, 14, 15, 16 — fifteen of the sixteen (Fact 7 is occurrence-level, out).
- **§3.4 laws**: all unconditional equivalences and s-equivalences (D1–D3, D7, D9, D10, D16, D17, D19–D27, D30, D31, D34–D38, D40, D41, D43–D46, D48), the "iff test" laws (D18, D19), the conditional laws with AQV/FV side conditions (D14, D32, D33, D39, D42, D47), and ≥ 6 non-equivalence countermodels (D4, D5, D6, D8, D11/D12, D18-instance `¬¬∃xPx ≢ ∃xPx`, D28, D29, D49, Fact 3).
- **Entailment** Def. 18–22 (s-entailment, meaning inclusion, dynamic entailment, x̄-entailment, sequence entailment); Facts 10–16; the source's separating examples (`⊨ₛ ∃xPx → Px` yet `∃xPx ⊭ₛ Px`; `∃xPx ⊨ Px`; `∃xPx ⋠ Px`; non-reflexivity of ⊨; non-transitivity `¬¬∃xPx, ∃xPx, Px`; mutual entailment without equivalence).
- **Donkey theorems**: `dk1` "A farmer owns a donkey. He beats it." (the (1b)-shaped cross-sentential conjunction, P 41 / §2.3), `dk2` "If a farmer owns a donkey, he beats it." ((2b), P 42 / §2.4), each with (i) the relational meaning and (ii) the first-order truth condition as a Coq proposition, proved as biconditionals for every domain and interpretation; `dk3` (3b) "Every farmer who owns a donkey beats it" and `equiv dk2 dk3` via D48.
- **Fact 6 refutation** and the Def. 12 discrepancy as theorems/comments.

### STRETCH (in priority order)
1. Def. 22 ⇔ conjunction of premisses (P 70 display); order-sensitivity and non-monotonicity of sequence entailment (P 70).
2. The worked examples of §2.3–2.5: ⟦∃xPx ∧ Qx⟧ (P 46), ⟦∃xPx → Qx⟧ (P 49), ⟦¬∃xPx ∧ Qx⟧ and `¬∃xPx ∧ Qx ≃ Qx ∧ ¬∃xPx` (P 51–52); park sentence (1b) `∃x[Mx ∧ Wx] ∧ Whx` truth condition (P 41, 46).
3. D13, D15 (the "iff test" prose laws), D20 (`♦φ ≃ ♦ψ ⇔ φ ≃ₛ ψ`), D32-example `Px ∧ ∃xPx ≃ [Px ∧ ∃xPx] ∧ [Px ∧ ∃xPx]`.
4. Refutation of the P 62 rider "∃xφ is a test … only if φ is a contradiction" via `∃x∀y(y = x)`.
5. D50 with a DPL-aware substitution and the corrected side condition ("y does not occur in φ").
6. `Setoid`/`Proper` instances so `rewrite` works modulo `rel_eq`/`equiv` (convenience only; no theorem may depend on it).

### Deliberately out
- Occurrence-level `bp`, `aq`, `fv`, `sp` (Def. 13–14), Fact 7 (the source itself says its Def. 13 is "a bit sloppy" for lack of an occurrence notation; every later Fact uses only the variable-level `FV`/`AQV`).
- §4.1 (Def. 23–24, Facts 17–24: PL comparison, normal binding form), §4.2 DRT (Facts 25–27), §4.3 QDL (Facts 28–29), §5 — sibling atlas files.
- The natural-deduction system (announced P 70, not in the paper).
- Arity enforcement by typing (see artifact (iv)).

---

## 2. Representation decisions (definitive, with justification)

| Source notion | Coq encoding | Why |
|---|---|---|
| variables | `Definition Var := nat` | the source's variables are symbols with (silently) decidable identity; `Nat.eq_dec` gives `upd`, `in_dec` on FV/AQV lists, and `discriminate` for `0 ≠ 1` in countermodels. No section parameter: it would force every countermodel to re-instantiate it and complicates universe checks on `exists M`. |
| non-logical vocabulary | `Record signature := { Pred : Type; arity : Pred -> nat; Const : Type }` | one object to quantify over (`forall Σ`); concrete modules build `Σ_ex`, `Σ_dk`. |
| terms, formulas | `Inductive term Σ := TVar : Var -> term \| TCon : Const Σ -> term`; `Inductive form Σ := Atom : Pred Σ -> list (term Σ) -> form \| Eq \| Neg \| Conj \| Disj \| Impl \| Ex : Var -> form -> form \| All : Var -> form -> form` | Def. 1 verbatim; all eight connectives primitive so D1–D3 are theorems, not definitions. `list term` for `t1…tn` (Vector rejected: dependent induction friction in the transfer lemma). |
| model ⟨D,F⟩ | `Record model Σ := { D : Type; D_inh : D; F_con : Const Σ -> D; F_pred : Pred Σ -> list D -> Prop }` | "F(R) ⊆ Dⁿ" as a predicate on lists; `D_inh` records non-emptiness (used only by the Fact 6 refutation and countermodels). |
| assignments G, ⟦t⟧_g | `G M := Var -> D M`; `tval M g t` | total, as in the source. |
| `g[x := d]`, `k[x]g` | `upd g x d := fun y => if Nat.eq_dec y x then d else g y`; `diff x k g := forall y, y <> x -> k y = g y` | `diff` is the source's gloss "differs at most in x" (P 45); pointwise so that witnesses are cheap. With funext: `diff_iff_upd : diff x k g <-> exists d, k = upd g x d`. |
| relations, sets | `Rel M := G M -> G M -> Prop`; `rel_eq R S := forall g h, R g h <-> S g h`; sets of assignments are `G M -> Prop` | never Leibniz `=` on relations (would need propositional extensionality, never needed). |
| Def. 2 | `rtest P g h := h = g /\ P h`; `rcomp R S g h := exists k, R g k /\ S k h`; `rneg R := rtest (fun h => ~ exists k, R h k)`; `rdisj R S := rtest (fun h => exists k, R h k \/ S h k)`; `rimpl R S := rtest (fun h => forall k, R h k -> exists j, S k j)`; `rex x R g h := exists k, diff x k g /\ R k h`; `rall x R := rtest (fun h => forall k, diff x k h -> exists j, R k j)`; `sem M : form Σ -> Rel M` by structural recursion through these | unfolding `sem` on a formula yields Def. 2's set-builder literally (orientation `h = g`, quantification over `h` inside the test clauses, ∀-clause quantifying `k[x]h`). Validated by the probe. |
| Def. 17 ♦ | `rclos R := rtest (fun h => exists k, R h k)`; formula level `Clos φ := Neg (Neg φ)` with `sem_clos : rel_eq (sem (Clos φ)) (rclos (sem φ))` (classical) | ♦ is not in Def. 1; the source's own D19 `♦φ ≃ ¬¬φ` licenses the surrogate. Displays mentioning ♦ are stated with `Clos` at formula level (and, where illuminating, with `rclos` at relation level). |
| equality of assignments | Leibniz `=`, with `FunctionalExtensionality` imported globally; `assign_ext : (forall y, h y = g y) -> h = g` | the source's `g = h` (Def. 2, Def. 11) is equality of set-theoretic functions, i.e. extensional. Without it the transfer lemma cannot conclude `sem (Neg φ) g' g'` from pointwise data, and D32/D33/D47, Fact 6's refutation and `upd g x (g x) = g` are unprovable. Usage is tracked with `Print Assumptions`; the headline theorems avoid it. |
| ≃, ≃ₛ, ≃ₚ, ≼ | `equiv φ ψ := forall M, rel_eq (sem M φ) (sem M ψ)` (Def. 8); `s_equiv` (Def. 7) on `sat_set`; `p_equiv` (Def. 10) on `prod_set`; `meaning_incl` (Def. 19) pointwise ⊆ | the source's "∀M" ranges over models of the ambient signature; signature-polymorphic statements are explicit `forall Σ`. |
| ≢ (schema not valid) | primary form `exists (M : model Σ_ex) g h, sem M φ g h /\ ~ sem M ψ g h` for a concrete instance, plus the schematic corollary `~ (forall Σ (φ ψ : form Σ), equiv φ ψ)` | matches the brief's requested `exists model formula, …` shape; concrete instance is what the source gives. |
| tests, conditions | `test φ := forall M g h, sem M φ g h -> g = h` (Def. 11, Leibniz); `Inductive condition : form Σ -> Prop` with atom, `=`, ¬, ∨, →, **∀** (added), and ∧ of conditions | Def. 12 as printed omits ∀xφ in both editions; the prose immediately before it (and Fact 5 with the ∀ clause of Def. 2) require it; comment `(* SOURCE NOTE: Def. 12 omits ∀; added per P 57 prose *)`. |
| FV, AQV (Def. 15–16) | `Fixpoint AQV : form -> list Var`: `AQV (Conj φ ψ) = AQV φ ++ AQV ψ`, `AQV (Ex x φ) = x :: AQV φ`, `[]` otherwise. `Fixpoint FV`: atoms/`=` = variables of the terms; `FV (Neg φ) = FV φ`; `FV (Conj φ ψ) = FV (Impl φ ψ) = FV φ ++ (FV ψ \ AQV φ)` (`filter` with `in_dec`); `FV (Disj φ ψ) = FV φ ++ FV ψ`; `FV (Ex x φ) = FV (All x φ) = remove Nat.eq_dec x (FV φ)` | exactly the variable-level projection of Def. 13 (the "de-activation" subtlety of `aq` disappears at variable level: `AQV` is a set, duplicates harmless). Side condition `AQV(φ) ∩ FV(ψ) = ∅` is `disjoint (AQV φ) (FV ψ) := forall v, In v (AQV φ) -> ~ In v (FV ψ)`. `agree V g h := forall v, In v V -> g v = h v` is the source's `g =_V h`. |
| entailments | `s_entails` (Def. 18); `entails φ ψ := forall M g h, sem M φ g h -> true_wrt M ψ h` (Def. 20); `entails_vars (xs : list Var)` (Def. 21); `sem_seq M (Γ : list form)` = chained `rcomp` starting from the identity, `entails_seq Γ ψ` (Def. 22) | Def. 22's "a *sequence*, not a set" is literal: a list. |
| classical logic | `From Coq Require Import Classical` globally | the source's metatheory is classical; D1, D2, D7, D9, D10, D17–D26, D40–D42, D14, Fact 3, Fact 12 need `classic`/`NNPP`. Constructive proofs where free. |
| notations | `Declare Scope dpl_scope`, `φ ∧' ψ` (80, right), `φ ∨' ψ` (85), `φ →' ψ` (90, right), `¬' φ` (75), `∃' x , φ` and `∀' x , φ` (95, `x at level 0`); used as `(…)%dpl`; never `Open Scope dpl_scope` globally | primed glyphs avoid every clash with Coq's own connectives; validated by the probe. |

Concrete signatures: `Σ_ex` (`Inductive pred_ex := P | Q | R2`, arities 1, 1, 2, `Const := Empty_set`) with `M_bool` (`D := bool`, `F_pred _ [d] := d = true`, `F_pred _ _ := False` otherwise; a variant `M_boolQ` with `Q` interpreted as `{false}` for D29) and `M_one` (`D := unit`) — `Σ_dk` (`Inductive pred_dk := farmer | donkey | own | beat`) with `M_dk` built from Coq relations `Fa Dk : Dm -> Prop`, `Ow Bt : Dm -> Dm -> Prop` over an arbitrary inhabited `Dm`.

---

## 3. Definitions (numbered, with source references)

**Prelim / syntax / models**
1. `Var := nat`; list-set helpers `disjoint`, `agree V g h` (= `g =_V h`, P 61 preamble to Fact 8 and Def. 21 P 69).
2. `signature`, `term`, `form` — Def. 1 (P 53 / T 13); `Arguments` so `Σ` is implicit in constructors; `size φ` (for `Eval compute` sanity checks only).
3. `wf_arity φ` (all atoms have `length ts = arity R`) — defined, not a hypothesis of any theorem (artifact (iv)).
4. `model Σ`, `G M`, `Rel M`, `tval M g t` (⟦t⟧_g) — P 53–54 / T 14.
5. `upd`, `diff x k g` (`k[x]g`) — §2.3 P 45; lemmas `upd_eq`, `upd_neq`, `diff_upd`, `diff_refl`, `diff_sym`, `diff_iff_upd` (funext), `upd_same : upd g x (g x) = g` (funext).

**Relation layer and semantics**
6. `rel_eq`, `rel_incl`; `rtest`, `rcomp`, `rneg`, `rdisj`, `rimpl`, `rex`, `rall` — the eight clauses of Def. 2 (P 54 / T 14), plus `ratom M R ts`, `req M t1 t2`.
7. `rclos` — Def. 17 (P 63 / T 22); `sat R g := exists h, R g h`, `prod R h := exists g, R g h`, `is_test_rel R := forall g h, R g h -> g = h`.
8. `sem M φ : Rel M` — Def. 2; eight unfolding lemmas `sem_atom … sem_all` (`reflexivity`), `sem_clos` (classical).

**Semantic notions (§3.2)**
9. `true_wrt M φ g := exists h, sem M φ g h` — Def. 3 (P 55).
10. `valid φ`, `contradiction φ` — Def. 4–5 (P 55).
11. `sat_set M φ : G M -> Prop` (`\φ\_M`) — Def. 6 (P 55); `prod_set M φ` (`/φ/_M`) — Def. 9 (P 56).
12. `s_equiv`, `equiv`, `p_equiv` — Def. 7, 8, 10 (P 56).
13. `test φ` — Def. 11 (P 57); `condition` — Def. 12 (P 57, ∀ added).
14. `Clos φ := Neg (Neg φ)` — formula-level ♦ (Def. 17 via D19).

**Binding (§3.3, variable level)**
15. `term_vars`, `AQV`, `FV` — Def. 16, 15 (P 61 / T 19) read through Def. 13 (P 58–59); characterisation lemmas `In_AQV_conj`, `In_AQV_ex`, `In_FV_conj`, `In_FV_impl`, `In_FV_ex`, `In_FV_all`, `In_FV_disj`, `In_FV_neg`, `AQV_test_nil : condition φ -> AQV φ = []`.

**Entailment (§3.5)**
16. `s_entails` — Def. 18 (P 66); `meaning_incl` — Def. 19 (P 66); `entails` — Def. 20 (P 67) with `entails_iff_prod_sub_sat` (the "more economically" form); `entails_vars xs φ ψ := forall M g, prod_set M φ g -> exists h, sem M ψ g h /\ agree xs h g` — Def. 21 (P 69); `sem_seq M Γ`, `entails_seq Γ ψ` — Def. 22 (P 70); `big_conj φ Γ` (right-nested).

**Concrete signatures and formulas**
17. `Σ_ex`, `M_bool`, `M_boolQ`, `M_one`, `g0 := fun _ => false`, `h1 := upd g0 0 true`; abbreviations `Px := @Atom Σ_ex P [TVar 0]`, `Qx`, `Py := @Atom Σ_ex P [TVar 1]`.
18. `Σ_dk`, `M_dk Dm d0 Fa Dk Ow Bt`; `x := 0`, `y := 1`; `dk1 := (∃'x, (farmer x ∧' ∃'y, (donkey y ∧' own x y))) ∧' beat x y` ("A farmer owns a donkey. He beats it.", P 41 shape (1b)); `dk2 := (∃'x, (…)) →' beat x y` (= (2b), P 42); `dk3 := ∀'x, ((farmer x ∧' ∃'y, (donkey y ∧' own x y)) →' beat x y)` (= (3b), P 42); STRETCH `park := (∃'x, (man x ∧' walk x)) ∧' whistle x` (= (1b), P 41).

---

## 4. Theorems (numbered; MUST/STRETCH; source; proof strategy). Difficulty E ≤ 15 lines, M 15–60, H > 60. Cl = uses `classic`, Fx = uses funext.

### 4.1 Relation layer and clause lemmas (all MUST, E)
- **R1** `sem_*` unfolding lemmas, `reflexivity`.
- **R2** `rtest_is_test`, hence `test_atom`, `test_eq`, `test_neg`, `test_disj`, `test_impl`, `test_all`, `test_clos`; `test_conj : test φ -> test ψ -> test (Conj φ ψ)` — Def. 11 remark (P 57), §2.4 P 49 (→ "has the character of a test"), §2.5 P 50 (∀).
- **R3** `sat_rtest : sat (rtest P) g <-> P g`; `sat_rneg : sat (rneg R) g <-> ~ sat R g`; `true_wrt_test : test φ -> (true_wrt M φ g <-> sem M φ g g)` (P 57 "boils down to ⟨g,g⟩ ∈ ⟦φ⟧").
- **R4** `not_test_ex : ~ test (Ex 0 Px)` over `Σ_ex` (`M_bool`, `g0`, `h1`, apply `f_equal (fun f => f 0)`; `discriminate`) — the dynamic side of the static/dynamic distinction. E.
- **R5** congruence lemmas `equiv_neg`, `equiv_conj`, `equiv_disj`, `equiv_impl`, `equiv_ex`, `equiv_all`, `equiv_refl/sym/trans` (used to chain displays; `Proper` instances are STRETCH 6).

### 4.2 §3.2 Facts (MUST)
- **Fact 1** (P 56) `equiv φ ψ -> s_equiv φ ψ`. E.
- **Fact 2** (P 56) `equiv φ ψ -> p_equiv φ ψ`. E.
- **Fact 3** (P 56–57) witness form: `s_equiv (Px ∨' ¬'Px) (∃'0, (Px ∨' ¬'Px)) /\ p_equiv … /\ ~ equiv …`; sat/prod sets are all of G (Cl for `Px ∨ ¬Px`); non-equivalence via `(g0, h1)`. M, Cl.
- **Fact 4** (P 57) `test φ -> test ψ -> (s_equiv φ ψ <-> equiv φ ψ) /\ (equiv φ ψ <-> p_equiv φ ψ)`. M (collapse pairs to diagonals with `test`).
- **Fact 5** (P 58) `condition φ -> test φ`. E, induction on `condition` + R2.
- **Fact 6 (⇐)** (P 58) `condition φ \/ contradiction φ -> test φ`. E.
- **Fact 6 (⇒) refuted** `fact6_refuted : exists φ : form Σ_ex, test φ /\ ~ condition φ /\ ~ contradiction φ` with `φ := (TVar 0 =' TVar 1) ∧' ∃'0, (TVar 0 =' TVar 1)`: any output `h` satisfies `h[0]g`, `h 0 = h 1 = g 1 = g 0`, so `h` is pointwise `g`, `assign_ext` gives `h = g`; not a contradiction (true at the constant assignment in `M_one`, or at any `g` with `g 0 = g 1` in any model); not a condition (`inversion`). M, Fx. `(* SOURCE NOTE *)` explains that with identity in the language Fact 6 (⇒) is false; the equality-free fragment is not pursued.

### 4.3 §3.3 binding lemmas (MUST) — the technical core
- **Fact 9** (P 61) constructive form `fact9 : ~ In x (AQV φ) -> forall M g h, sem M φ g h -> g x = h x`; corollary `fact9_src` in the source's contrapositive shape (Cl). Induction on φ generalising `g h`; test cases by `destruct H as [-> _]`; Conj via `in_app_iff`; Ex via `diff`. M (probe-validated, 15 lines).
- **Corollary 9a** `outputs_agree_outside : sem M φ g h -> forall v, ~ In v (AQV φ) -> g v = h v`; **9b** `disjoint (AQV φ) (FV ψ) -> sem M φ g h -> agree (FV ψ) g h`.
- **T (transfer lemma)** — not stated in the source, but exactly the induction its proofs of Facts 8, 13, 14, 16 and D14/D32/D33/D39/D42/D47 rely on:
  `transfer : forall M φ g g' h, agree (FV φ) g g' -> sem M φ g h -> exists h', sem M φ g' h' /\ agree (AQV φ) h' h /\ (forall v, ~ In v (AQV φ) -> h' v = g' v)`.
  Induction on φ generalising `g g' h` (the statement is symmetric in `g, g'`, which the test cases need in both directions). Cases: atoms/`=`: `h' := g'` (agreement on `FV` makes the test pass). Neg: `h' := g'`; a witness `sem φ g' k` transfers back to `g` by IH, contradiction. Disj: like Neg, one IH per disjunct. Impl: given `sem φ g' k'`, IH (g' → g) yields `k` with `sem φ g k`, hence `j` with `sem ψ k j`; `agree (FV ψ) k k'` holds because on `AQV φ` they agree by IH and outside by Fact 9 + `agree (FV (Impl φ ψ)) g g'`; IH on ψ (k → k') gives the required `j'`. All: `k := upd g x (k' x)`, then like Impl. Conj: IH φ gives `k'`; `agree (FV ψ) k k'` as in Impl; IH ψ gives `h'`; the two agreement clauses are checked by cases on `In v (AQV ψ)`, `In v (AQV φ)` using Fact 9 on ψ. Ex: `k' := upd g' x (k x)`; `agree (FV φ) k k'` by cases on `v = x`; IH gives `h'`; agreement on `x :: AQV φ` uses Fact 9 when `x ∉ AQV φ`. H (≈ 120–180 lines). No funext, no classic.
- **Fact 8** (P 61) `agree (FV φ) g h -> (true_wrt M φ g <-> true_wrt M φ h)`. E from T (both directions by symmetry of `agree`).
- **T'** (A's form, derived, Fx) `transfer_given : agree (FV φ) g g' -> sem M φ g h -> agree (AQV φ) h h' -> (forall v, ~ In v (AQV φ) -> h' v = g' v) -> sem M φ g' h'` — from T and `assign_ext`. Used by D32/D33/D47. E.

### 4.4 §3.4 displayed laws (D-numbering = reading order T 20–25 / P 61–66)

Unconditional laws are proved at relation level (`forall R S T : Rel M`) and instantiated; the formula-level theorem is the one that carries the source comment. All MUST unless marked.

| D | Page | Statement | Kind | Strategy |
|---|---|---|---|---|
| D1 | P 61 | `φ →' ψ ≃ ¬'(φ ∧' ¬'ψ)` | ≃ | E, Cl (`not_ex_all_not`, `NNPP`) |
| D2 | P 61 | `φ ∨' ψ ≃ ¬'(¬'φ ∧' ¬'ψ)` | ≃ | E, Cl |
| D3 | P 61 | `∀'x, φ ≃ ¬'∃'x, ¬'φ` | ≃ | E, Cl |
| D4 | P 61 | `φ ∧' ψ ≢ ¬'(φ →' ¬'ψ)` | ≢ | instance `∃'0,Px ∧' Qx`, `M_bool`, `(g0,h1)`; RHS is a test. E |
| D5 | P 61 | `φ ∧' ψ ≢ ¬'(¬'φ ∨' ¬'ψ)` | ≢ | same instance. E |
| D6 | P 61 | `∃'x, φ ≢ ¬'∀'x, ¬'φ` | ≢ | instance `∃'0,Px`. E |
| D7 | P 62 | `φ ∧' ψ ≃ₛ ¬'(φ →' ¬'ψ)` | ≃ₛ | M, Cl |
| D8 | P 62 | `φ ∧' ψ ≢ₛ ¬'(¬'φ ∨' ¬'ψ)` | ≢ₛ | instance `∃'0,Px ∧' Qx` vs RHS in `M_bool`, `g0` (`P = Q = {true}`): LHS true, RHS false. M |
| D9 | P 62 | `∃'x, φ ≃ₛ ¬'∀'x, ¬'φ` | ≃ₛ | M, Cl |
| D10 | P 62 | `φ ∨' ψ ≃ ¬'φ →' ψ` | ≃ | E, Cl |
| D11 | P 62 | `φ →' ψ ≢ ¬'φ ∨' ψ` | ≢ | instance `∃'0,Px →' Qx` vs `¬'∃'0,Px ∨' Qx`, `M_bool`, `g0`. M |
| D12 | P 62 | `φ →' ψ ≢ₛ ¬'φ ∨' ψ` | ≢ₛ | same instance (hence D11). M |
| D13 | P 62 prose | `equiv (φ ∧' ψ) (¬'(φ →' ¬'ψ)) <-> test (φ ∧' ψ)` | iff | M, Cl. **STRETCH** |
| D14 | P 62 prose | `disjoint (AQV φ) (FV ψ) -> equiv (φ →' ψ) (¬'φ ∨' ψ)` | cond. ≃ | Cl; `classic (exists k, sem φ g k)`, then Fact 9b + Fact 8 to move the ψ-witness between `k` and `g`. M |
| D15 | P 62 prose | `equiv (∃'x, φ) (¬'∀'x, ¬'φ) <-> test (∃'x, φ)` | iff | E. **STRETCH**; the rider "only if φ is a contradiction" refuted by `∃'0, ∀'1, (TVar 1 =' TVar 0)` in `M_one` (STRETCH 4, Fx) |
| D16 | P 62 | `¬'∃'x, φ ≃ ∀'x, ¬'φ` | ≃ | E, constructive |
| D17 | P 62 | `φ ≃ₛ ¬'¬'φ` | ≃ₛ | E, Cl |
| D18 | P 62 | `equiv (¬'¬'φ) φ <-> test φ` | iff | M, Cl (⇐ via `NNPP` after `h = g`); plus the **headline countermodel** `negneg_witness : exists (M : model Σ_ex) φ g h, sem M φ g h /\ ~ sem M (¬'¬'φ) g h` (probe-validated, axiom-free) and `~ equiv (¬'¬'∃'0,Px) (∃'0,Px)` |
| D19 | P 63 | `Clos φ ≃ ¬'¬'φ` (refl); `equiv (Clos φ) φ <-> test φ` | ≃ / iff | E (D18) |
| D20 | P 63 | `equiv (Clos φ) (Clos ψ) <-> s_equiv φ ψ` | iff | E, Cl. **STRETCH** |
| D21 | P 63 | `Clos (Clos φ) ≃ Clos φ ≃ ¬'¬'φ` | ≃ | E, Cl |
| D22 | P 63 | `Clos (¬'φ) ≃ ¬'φ ≃ ¬'(Clos φ)` | ≃ | E, Cl |
| D23 | P 63 | `Clos (φ ∧' ψ) ≃ ¬'(φ →' ¬'ψ)` | ≃ | E, Cl |
| D24 | P 63 | `Clos φ ∧' Clos ψ ≃ ¬'(¬'φ ∨' ¬'ψ)` | ≃ | M, Cl |
| D25 | P 63 | `Clos (∃'x, φ) ≃ ¬'∀'x, ¬'φ` | ≃ | E, Cl |
| D26 | P 63 | `Clos φ →' ψ ≃ ¬'φ ∨' ψ` | ≃ | M, Cl |
| D27 | P 63 | `(φ ∧' ψ) ∧' χ ≃ φ ∧' (ψ ∧' χ)` — **associativity** | ≃ | E, constructive (`rcomp_assoc`, probe-validated) |
| D28 | P 63 | `φ ∧' ψ ≢ ψ ∧' φ` | ≢ | instance `∃'0,Px ∧' Qx` vs `Qx ∧' ∃'0,Px`, `M_bool`, `(g0,h1)`. E |
| D29 | P 63 | `φ ≢ φ ∧' φ` | ≢ | instance `Qx ∧' ∃'0,Px` in `M_boolQ` (`Q = {false}`, `P = {true}`): `(g0,h1)` in LHS, not in RHS. E. Typescript prints `ψ ∧ φ`; journal `φ ∧ φ` (SOURCE NOTE) |
| D30 | P 64 | `Clos φ ∧' Clos ψ ≃ Clos ψ ∧' Clos φ` | ≃ | E |
| D31 | P 64 | `Clos φ ≃ Clos φ ∧' Clos φ` | ≃ | E |
| D32 | P 64 | `disjoint (AQV φ) (FV φ) -> φ ≃ φ ∧' φ` | cond. ≃ | ⇒: `k := h`, `sem φ h h` by T' (`agree (FV φ) g h` from Fact 9b); ⇐: from `sem φ g k`, `sem φ k h` get `sem φ g h` by T' (agree on FV between `g` and `k` by Fact 9b). M, Fx |
| D32e | P 64 | `Px ∧' ∃'0,Px ≃ (Px ∧' ∃'0,Px) ∧' (Px ∧' ∃'0,Px)` | ≃ | direct witnesses. E. **STRETCH** |
| D33 | P 64 | `disjoint (AQV φ) (FV ψ) -> disjoint (AQV ψ) (FV φ) -> disjoint (AQV φ) (AQV ψ) -> φ ∧' ψ ≃ ψ ∧' φ` | cond. ≃ | given `sem φ g k`, `sem ψ k h`: T on ψ (k → g) gives `k'`; T on φ (g → k') gives `h'`; show `h' = h` pointwise by cases on membership in `AQV φ`, `AQV ψ` (Fact 9 on both), then `assign_ext`. Symmetric direction identical. H, Fx |
| D34 | P 64 | `φ ≃ φ ∨' φ` | ≃ | E |
| D35 | P 64 | `φ ∨' ψ ≃ ψ ∨' φ` | ≃ | E |
| D36 | P 64 | `φ ∨' (ψ ∨' χ) ≃ (φ ∨' ψ) ∨' χ` | ≃ | E |
| D37 | P 64 | `Clos (φ ∧' (ψ ∨' χ)) ≃ (φ ∧' ψ) ∨' (φ ∧' χ)` | ≃ | M, constructive |
| D38 | P 64 | `φ ∨' (Clos ψ ∧' χ) ≃ (φ ∨' ψ) ∧' (φ ∨' χ)` | ≃ | M, Cl (`h = g` in both conjuncts of RHS) |
| D39 | P 64 | `disjoint (AQV ψ) (FV χ) -> φ ∨' (ψ ∧' χ) ≃ (φ ∨' ψ) ∧' (φ ∨' χ)` | cond. ≃ | Fact 9b + Fact 8 to move the χ-witness. M |
| D40 | P 65 | `(¬'φ →' ψ) ≃ (¬'ψ →' φ)` | ≃ | E, Cl |
| D41 | P 65 | `(Clos φ →' ψ) ≃ (¬'ψ →' ¬'φ)` | ≃ | E, Cl |
| D42 | P 65 | `disjoint (AQV φ) (FV ψ) -> (φ →' ψ) ≃ (¬'ψ →' ¬'φ)` | cond. ≃ | Cl + Fact 9b + Fact 8. M |
| D43 | P 65 | `(φ →' ψ) ≃ Clos (φ →' ψ)` | ≃ | E |
| D44 | P 65 | `(φ →' ψ) ≃ (φ →' Clos ψ)` | ≃ | E |
| D45 | P 65 | `φ →' (ψ →' χ) ≃ (φ ∧' ψ) →' χ` | ≃ | E, constructive |
| D46 | P 65 | `∃'x, φ ∧' ψ ≃ ∃'x, (φ ∧' ψ)` — **Egli's Theorem** (Dekker 2012 Obs. 1) | ≃ | E, constructive (`rcomp_rex`, probe-validated) |
| D47 | P 65 | `~ In x (FV φ) -> ~ In x (AQV φ) -> φ ∧' ∃'x, ψ ≃ ∃'x, (φ ∧' ψ)` | cond. ≃ | ⇒: `j := upd g x (k' x)`, T' on φ (g → j) with target output `k'`; ⇐: T on φ (j → g) gives `k'`, then `diff x k k'` by Fact 9. M, Fx |
| D48 | P 65 | `(∃'x, φ) →' ψ ≃ ∀'x, (φ →' ψ)` — **Egli's Corollary**, "important for donkey cases" | ≃ | E, constructive (`rimpl_rex`, probe-validated) |
| D49 | P 66 | `∃'x, φ ≢ ∃'y, [y/x]φ` — instance `∃'0,Px ≢ ∃'1,Py`, and `s_equiv (∃'0,Px) (∃'1,Py)` (Fact 1 converse fails, P 56) | ≢ | production sets differ: `(g0, h1)` is in LHS not RHS. E |
| D50 | P 66 | `y ∉ FV φ -> ∃'x, φ ≃ₛ ∃'y, [y/x]φ` | ≃ₛ | **STRETCH 5**; needs a DPL-aware substitution and the stronger hypothesis "y does not occur in φ" (the printed side condition is refuted by `φ := ∃y R2 x y`; SOURCE NOTE) |

Count: 33 unconditional/iff equivalence laws MUST, 6 conditional laws MUST, 9 countermodels MUST (D4, D5, D6, D8, D11/12, D18-instance, D28, D29, D49) + Fact 3.

### 4.5 §3.5 entailment (MUST)
- **Fact 10** (P 67) `meaning_incl φ ψ -> s_entails φ ψ`. E.
- **Fact 11 (Deduction theorem)** (P 67) `entails φ ψ <-> valid (φ →' ψ)`. E.
- **Fact 12** (P 67) `s_entails φ ψ <-> entails (Clos φ) ψ`. E, Cl.
- **Fact 13** (P 68) `disjoint (AQV φ) (FV ψ) -> (s_entails φ ψ <-> entails φ ψ)`. E from Fact 9b + Fact 8.
- **Fact 14** (P 68) `disjoint (AQV φ) (FV ψ) -> meaning_incl φ ψ -> entails φ ψ`. E, the source's proof verbatim.
- **Fact 15 (Reflexivity)** (P 68) `disjoint (AQV φ) (FV φ) -> entails φ φ`. E from Fact 14.
- **E-weak** (P 68 unnumbered) `disjoint (AQV ψ) (FV ψ) -> entails (φ ∧' ψ) ψ`. E.
- **Def. 21 lemmas** `entails_vars_nil : entails_vars [] φ ψ <-> entails φ ψ`; `entails_vars_entails : entails_vars xs φ ψ -> entails φ ψ` (P 69). E.
- **Fact 16 (Transitivity)** (P 69) `entails_vars (inter (AQV ψ) (FV χ)) φ ψ -> entails ψ χ -> entails φ χ`; the source's proof: for `v ∈ FV χ`, `g v = h v` either by the `entails_vars` clause (`v ∈ AQV ψ`) or by Fact 9 (`v ∉ AQV ψ`), then Fact 8. M.
- **Separating examples** over `Σ_ex` (P 67–69), each a concrete theorem: `valid (∃'0,Px →' Px)`; `~ s_entails (∃'0,Px) Px`; `entails (∃'0,Px) Px`; `~ meaning_incl (∃'0,Px) Px`; `entails Px (∃'0,Px) /\ ~ equiv (∃'0,Px) Px` (mutual entailment without equivalence); `meaning_incl (Qx ∧' ∃'0,Px) (Qx ∧' ∃'0,Px) /\ ~ entails (Qx ∧' ∃'0,Px) (Qx ∧' ∃'0,Px)` (non-reflexivity; `M_boolQ`); `entails (¬'¬'∃'0,Px) (∃'0,Px) /\ entails (∃'0,Px) Px /\ ~ entails (¬'¬'∃'0,Px) Px` (non-transitivity; `M_bool`, `g0`). M total.
- **STRETCH 1**: `entails_seq (φ :: Γ) ψ <-> entails (big_conj φ Γ) ψ <-> valid (big_conj φ Γ →' ψ)` (P 70); `entails_seq [∃'0,Px; ∃'0,Qx] Qx /\ ~ entails_seq [∃'0,Qx; ∃'0,Px] Qx`; left weakening `entails φ ψ -> entails_seq [χ; φ] ψ`; non-monotonicity `entails (∃'0,Px) Px /\ ~ entails_seq [∃'0,Px; ∃'0,Qx] Px` (P 70).

### 4.6 Donkey theorems (MUST) — `Section` over `Dm d0 Fa Dk Ow Bt`, `x := 0`, `y := 1`
- **DK1** "A farmer owns a donkey. He beats it." (P 41 shape (1b), §2.3): `dk1_meaning : sem M_dk dk1 g h <-> (forall v, v <> x -> v <> y -> h v = g v) /\ Fa (h x) /\ Dk (h y) /\ Ow (h x) (h y) /\ Bt (h x) (h y)` (⇐ needs `assign_ext` to identify `h` with `upd (upd g x (h x)) y (h y)`: Fx); `dk1_truth : true_wrt M_dk dk1 g <-> exists a b, Fa a /\ Dk b /\ Ow a b /\ Bt a b` (axiom-free; witness `upd (upd g x a) y b` used as the *same term* at every test step; probe-validated). M.
- **DK2** "If a farmer owns a donkey, he beats it." ((2b) P 42, §2.4; Dekker 2008 (17)): `dk2_meaning : sem M_dk dk2 g h <-> h = g /\ forall a b, Fa a -> Dk b -> Ow a b -> Bt a b`; `dk2_truth : true_wrt M_dk dk2 g <-> forall a b, Fa a -> Dk b -> Ow a b -> Bt a b` — the truth conditions of (2a) `∀x∀y[[farmer x ∧ donkey y ∧ own x y] → beat x y]` (P 41). Axiom-free (probe-validated). M.
- **DK3** (3b) "Every farmer who owns a donkey beats it" (P 42; computation §2.5 P 50–51): `equiv dk2 dk3` by D48 (E), hence `dk3_truth` by transport (E).
- **DK4** the Dekker 2008 p. 15 chain `dk2 ≃ dk3 ≃ ∀'x, (farmer x →' (∃'y, (donkey y ∧' own x y) →' beat x y)) ≃ ∀'x, (farmer x →' ∀'y, ((donkey y ∧' own x y) →' beat x y))` by D45, D48 and R5 congruence. E. **STRETCH 2**.
- **STRETCH 2** `park_truth : true_wrt M park g <-> exists a, Man a /\ Walk a /\ Whistle a` (P 41, 46); worked examples ⟦∃xPx ∧ Qx⟧ = `{(g,h) | h[x]g ∧ P(h x) ∧ Q(h x)}` (P 46), `equiv (∃'0,Px ∧' Qx) (∃'0,(Px ∧' Qx))` (P 46 "no difference in meaning"), ⟦∃xPx → Qx⟧ (P 49), `equiv (∃'0,Px →' Qx) (∀'0,(Px →' Qx))`, ⟦¬∃xPx ∧ Qx⟧ (P 51–52) and `equiv (¬'∃'0,Px ∧' Qx) (Qx ∧' ¬'∃'0,Px)` (P 52).

### 4.7 Axiom audit (MUST)
`Print Assumptions` for: D27, D46, D48, `negneg_witness`, `fact9`, `dk1_truth`, `dk2_truth` (expected: closed); D1, D18, Fact 3, Fact 12 (expected: `classic` only); D32, D33, D47, `fact6_refuted`, `dk1_meaning` (expected: `functional_extensionality_dep`, possibly `classic`). Summarised in a header table.

---

## 5. Expected encoding artifacts (each flagged in-file as `(* ARTIFACT (k): … *)`, indexed in the header)

- **(i) Strict positivity** — none. `form` is first-order; `condition` is a plain inductive predicate; `sem` must be a `Fixpoint` into `Prop`, *not* an `Inductive` relation: the ¬, →, ∀ clauses contain `~ exists` / `forall … -> exists`, which would be non-positive occurrences. Documented at `sem`.
- **(ii) Universe / type–value collapse** — `model Σ` contains `D : Type`, so `equiv`, `valid`, `test`, `entails` quantify over a large type inside `Prop` (impredicativity; harmless). The source's sets (`F(R) ⊆ Dⁿ`, `⟦φ⟧ ⊆ G × G`, `\φ\`, `/φ/`) are `Prop`-valued functions; set identity is `rel_eq`/pointwise `<->`, never Leibniz. Countermodels are `exists M : model Σ_ex, …` with a `Type`-level witness inside `Prop` (allowed). Documented at `model`, `rel_eq`, `equiv`.
- **(iii) Computational opacity** — `sem`, `true_wrt`, `test`, `equiv`, `entails` never compute; countermodels are proved, not evaluated; `classic` blocks any computational reading of `¬¬`. Only `upd`, `tval`, `AQV`, `FV`, `size` compute; `Eval compute in AQV dk1` (= `[0; 1]`), `FV dk2` (= `[]`), `FV (Qx ∧' ∃'0,Px)` (= `[0]`) are included as sanity checks.
- **(iv) Missing native structure** — (a) extensional equality of assignments: added by `FunctionalExtensionality` (justified in §2); (b) occurrences (Def. 13–14, Fact 7) have no representation; `FV`/`AQV` are their variable-level shadows, which is all the Facts and displays use; (c) fixed arity is not enforced (`list D -> Prop`, `wf_arity` unused); (d) ♦ is not syntax — `rclos` at relation level, `Clos = ¬¬` at formula level, licensed by D19; (e) premiss *sequences* (Def. 22) are `list form` with a chain relation; (f) the source's "∀M" is over a fixed signature — explicit `forall Σ` where a statement is signature-polymorphic.
- **(v) Decidability gap** — `Var = nat` supplies decidable equality the source never states but uses (`upd`, occurrence comparison); `in_dec` on `AQV` is used to *compute* `FV` and to case-split in the transfer lemma. `classic` is used exactly where the source's set-theoretic reasoning is classical (listed per theorem in the audit).
- **Source discrepancies recorded as theorems/comments**: Def. 12 omits ∀ (fixed, noted); Fact 6 (⇒) false with identity (`fact6_refuted`); D15's rider "only if φ is a contradiction" false (`∃x∀y(y = x)`, STRETCH theorem, comment otherwise); D29 typo in the typescript; D50's printed side condition insufficient (capture); the printed proof of Fact 16 swaps the roles of ψ and χ in one line.

---

## 6. Pitfalls (Coq 8.20.1, stdlib only; ✔ = hit and fixed in the probe)

1. ✔ **Record notation cannot infer Σ.** `{| D := bool; F_con := …; F_pred := … |} : model Σ_ex` fails ("Found type Empty_set where Const ?Σ was expected") because `Const Σ_ex` only unfolds to `Empty_set` by delta. Write `@Build_model Σ_ex bool true (fun e : Empty_set => match e with end) (fun R ds => …)`. Likewise `Atom P [TVar 0]` fails to infer Σ from `P : pred_ex`: write `@Atom Σ_ex P [TVar 0]` (or define per-module smart constructors `Px`, `Qx`, `farmer_ t`, …). An unannotated `fun e => match e with end` is rejected ("matching with no clauses on a term unknown to have an empty inductive type"): annotate `e : Empty_set`.
2. ✔ **`ltac:(tauto)` inside a term application fails** when the goal contains evars (`rewrite (IH ltac:(tauto) …)`); use `assert (H : …) by tauto` first. In the `Ex` case of Fact 9 the inequality comes out as `v <> x`, the `diff` hypothesis wants `x <> v`: finish with `congruence`, not `assumption`.
3. ✔ **Intro-pattern `->` on chains of assignment equalities renames unpredictably** (`k = k4`, `k4 = k3`, `h = k` — `subst` picks which variable survives). In the donkey proofs name the equalities (`[E1 HF] … [E4 HB]`), use `subst k2 k4 k` explicitly, and bridge `Fa (k1 x)` to `Fa (k3 x)` with `rewrite <- (Hk3 x Hxy)` where `Hxy : x <> y` is `unfold x, y; discriminate`.
4. ✔ **`cbn in *` (not `simpl`) reduces `F_pred M_dk farmer (map (tval …) [TVar x])` to `Fa (k x)`** when `M_dk` is built with `Build_model` (transparent). Keep concrete models transparent `Definition`s; never `Opaque` them.
5. **Notation clash.** Coq's `∧ ∨ → ¬ ∃ ∀` are taken once `Utf8` is imported anywhere; use the primed forms in `dpl_scope` (validated: `(¬' ¬' ∃' 0, Px)%dpl` parses at the given levels; `x at level 0` is required in the binder notations). Never `Open Scope dpl_scope`.
6. **`simpl` on `sem`.** Because `sem` is layered, `simpl` on a compound formula stops at `rcomp (sem φ) (sem ψ)`; unfold `rcomp`/`rtest`/`rex` selectively (`unfold rcomp, rex; split; intros [k [Hk …]]`) rather than `simpl in *` on schematic φ ψ. For concrete formulas (`dk1`, countermodels) `simpl`/`cbn` gives the nested ∃-structure directly, which is what you want.
7. **Orientation.** Def. 2 says `h = g`; keep it in every clause lemma and destructure with `[-> H]` so `subst` replaces `h` by `g`; mixing orientations breaks `<->` chains silently.
8. **Function equality.** Use `assign_ext` (funext) only when a Leibniz output is *required* (test cases of T', D32/D33/D47, Fact 6). For witnesses in ∃-clauses, always supply the *same* `upd` term at every stage so the test steps close by `reflexivity`.
9. **Generalise before induction.** Fact 9 needs `forall g h` after the `~ In` hypothesis; the transfer lemma needs `g g' h` all universally quantified in the IH (the Impl/Conj/Ex cases instantiate them differently and the test cases use the IH with `g, g'` swapped).
10. **Classical lemma names.** `Classical_Pred_Type.not_all_not_ex`, `not_ex_all_not`, `not_all_ex_not`, `NNPP`, `classic`; `firstorder` will not find them and may loop on nested ∃ with equalities — write explicit `split; intros [k [H1 H2]]; subst; eauto` scripts.
11. **`In`/list reasoning.** Prove the `In_FV_*`/`In_AQV_*` characterisations once (`in_app_iff`, `filter_In`, `in_remove`, `negb_true_iff`) and never unfold `FV` afterwards; state `disjoint` as a `Prop` over `In`, never as list equality.
12. **Countermodel inequality of assignments**: `apply (f_equal (fun f => f 0)) in E; discriminate` (validated). `M_bool`'s `F_pred` must be total on all list lengths (`| _ => False`).
13. **Universe of `model`.** Keep `D : Type` (never `Set`); if `exists M : model Σ_ex` ever triggers a universe error inside a `Section`, state the witness theorem after the section with the concrete model as a top-level `Definition` (the probe needed no workaround).
14. **`Setoid` rewriting** (STRETCH 6 only): declare `Instance rel_eq_equiv : Equivalence rel_eq` and `Proper (rel_eq ==> rel_eq ==> rel_eq)` for `rcomp`, `rdisj`, `rimpl` and `Proper (rel_eq ==> rel_eq)` for `rneg`, `rex x`, `rall x`, `rclos`; until then chain laws with the `equiv_*` congruence lemmas of R5.
15. **Coq 8.20 specifics.** `lia` not `omega`; `From Coq Require Import` (the `Stdlib` prefix is 9.x); `Nat.eq_dec`; no `Program`/`Equations`; compile with `mkdir -p atlas/dynamic && coqc -R shallow "" -R deep "" -R extras "" -R ttr_mtt "" -R atlas "" atlas/dynamic/DPL.v` from the repo root; do not touch `_CoqProject`/`Makefile`.

---

## 7. Build order (each step compiles before the next; seed the file from the probe)

1. **Header + Prelim + Syntax + Models + relation layer + `sem` + clause lemmas** (Defs 1–8; R1). Copy from the probe. Add `assign_ext`, `diff_iff_upd`, `upd_same`.
2. **Notions and tests** (Defs 9–14; R2–R5; Facts 1, 2, 4, 5, 6⇐). `Eval compute` sanity checks.
3. **Countermodel module** `Σ_ex`/`M_bool`/`M_boolQ`/`M_one` and everything provable there without binding lemmas: R4, Fact 3, D4, D5, D6, D8, D11/D12, D18-instance (`negneg_witness`), D28, D29, D49, `fact6_refuted`, the entailment examples that need no Facts (`valid (∃'0,Px →' Px)`, `~ s_entails`, `entails`, `~ meaning_incl`, non-reflexivity, non-transitivity). (Entailment definitions from step 6 are needed for the last group — define Defs 16 early, in step 2, so this module is self-contained.)
4. **Relation-level laws and unconditional §3.4 displays**: D1–D3, D7, D9, D10, D16, D17, D18, D19, D21–D27, D30, D31, D34–D38, D40, D41, D43–D46, D48 (Egli, associativity and D48 first: they are the headline and the donkey step depends on D48).
5. **Binding**: `term_vars`, `AQV`, `FV`, characterisation lemmas, Fact 9 (+ 9a, 9b), transfer lemma T, Fact 8, T'; then the conditional displays D14, D39, D42 (no funext) and D32, D47, D33 (funext), in that order of increasing difficulty.
6. **Entailment**: Facts 10–16, `entails_vars` lemmas, remaining separating examples.
7. **Donkey module**: DK1, DK2, DK3 (via D48), audit block.
8. **STRETCH in the listed priority**: sequence-entailment lemmas and examples; §2 worked examples and DK4; D13, D15, D20, D32e; D15-rider refutation; D50 with substitution; `Proper` instances.
