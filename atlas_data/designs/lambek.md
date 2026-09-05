# Design: `atlas/type_logical/Lambek.v` — the associative Lambek calculus L

Target: `/Users/graogro/Dropbox/revisiting-formal-semantics/atlas/type_logical/Lambek.v` (single file, Coq 8.20.1, stdlib only, axiom-free; `atlas/` is empty so this file also sets the region's conventions).

**Judge's verdict.** Design A (syntax-first, deep de Bruijn λ-terms) is the base. The brief's Curry–Howard clause — "assign (linear) λ-terms to derivations, prove the substitution lemma for cut and that cut elimination preserves the term up to β" — is only *statable* with a syntactic term language and a syntactic `β*`; Design B's shallow reading (`den : cfderiv → sem_ctx → sem`) makes "up to β" definitional, so it cannot discharge that must-have (B's own §5(ii) concedes this). Both designs were spot-checked against the sources and are accurate; both agree on the sequent representation (`Γ1 ++ A :: Γ2`, `Γ <> []` side conditions on the right rules, derivations in `Type`, fuel-bounded transparent search with the connective-count bound). Grafted from Design B: the pre-ordered residuated semigroup with an explicit equivalence and the option-monoid lift of contexts (§2.9 unit remark), the Z-count model that yields the count invariant and cheap non-derivability results as instances of soundness, `ext_eq` (extensional equality at semantic types, so functional extensionality is never needed), the additional `vm_compute` examples (`s/(n\s) ⊬ n`, "a very book"), the Lambek-cases ↔ Coq-branches table inside cut admissibility, a semantic-invariance theorem for cut elimination as stretch, and pitfalls on `\/` lexing, `Entity : Type`, side-condition ordering and `Opaque`. Rejected from B: two derivation families (`cfderiv`/`deriv` — the flag index avoids duplicating `term`/`denote`/subformula lemmas), the triple nested structural induction for cut admissibility (Lambek's single measure with strong induction is simpler and is what Lambek and Moortgat actually use), `height` as the search bound (the connective count is the bound directly), and fixed atoms (the metatheory should be parametric; `sem` is defined at the `prim` instantiation).

Sources (verified against the PDFs): Moot & Retoré 2012 (M&R) ch. 2: §2.1 pp. 23–24, Fig. 2.2 p. 29, Prop 2.3 p. 29, Def 2.4/Prop 2.6 p. 30, Ex 2.7 p. 30, §2.5 p. 33 ("the antecedent … never is empty in a proof"; "a very book"), Prop 2.14 and Defs 2.15–2.16 p. 40, §2.7 pp. 40–43 (cases 1–4, "\ only, / symmetrical"), Thm 2.17 p. 43, Prop 2.18 pp. 43–44, §2.9 pp. 44–48 (unit remark p. 44, RSG and Prop 2.19 p. 45, free-group model p. 45 with `n ⊢ s/(n\s)` but not the converse, Prop 2.20 p. 46, powerset model p. 47, Prop 2.22 pp. 47–48); ch. 3: §3.3 pp. 74–75 (`S* = t, np* = e, n* = e→t, (a\b)* = (b/a)* = a*→b*`; the four-step algorithm; "Pierre ↦ λP (P Pierre)"), Ex 3.2 p. 76 (`some : (S/(np\S))/n ↦ λPλQ ∃x (Px ∧ Qx)`), Ex 3.5 pp. 81–84 (`every` subject `(S/(np\S))/n` and object `((S/np)\S)/n` with `λPλQ ∀x (Px ⇒ Qx)`, `ate : (np\S)/np ↦ λyλx (ate x y)`, two scope readings). Retoré 2005 §2.9 (cut elimination) and §2.14 (Montague, same homomorphism). Lambek 1958: §2 p. 155, §3 Table I p. 157, p. 159 (interpretation of types), §7 pp. 163–164 (rules (a)–(n)), §8 pp. 165–167 (sequents; rules (1),(2),(2′),(3),(3′),(4),(5) "provided T, P and Q are not empty"; cut (6) p. 166; decision procedure p. 167 "every upward step eliminates an occurrence of one of the connectives"), §9 pp. 167–169 (degree `d(T)+d(U)+d(V)+d(x)+d(y)`; "in any cut whose premises have been proved without cut … replaced by one or two such cuts of smaller degree"; Cases 1–7, Case 5 = product), §10 p. 169. Moortgat 1997: Def 2.13 p. 12, Prop 2.14 pp. 12–13 (cut complexity `d(Δ)+d(Γ)+d(Γ')+d(A)+d(B)`, "backward chaining"), Prop 2.18 p. 15, Def 3.2 p. 20 (`Ax x`, `Cut u[t/x]`, `→L u[y(t)/x]`, `→R λx.t`), Def 3.3/Prop 3.4 p. 20, Def 3.5 and Exs 3.6–3.7 p. 21.

---

## 1. Scope

### Formalized — MUST
- The product-free associative Lambek calculus L over an arbitrary set of primitive types, as a sequent calculus over `Γ ⊢ A` with `Γ : list formula`, with Lambek's "no empty antecedent" restriction as a side condition `Γ <> []` on the two right rules (M&R Fig. 2.2 `Γ ≠ ε`; Lambek §8), rules `ax`, `\L`, `\R`, `/L`, `/R`, `cut` (M&R Fig. 2.2 minus `•h/•i`; Lambek (1)–(3′),(6); Moortgat Def 2.13). Derivations are proof objects in `Type`.
- Non-emptiness of every derivable antecedent (theorem), atomic-axiom expansion (Prop 2.3).
- Cut admissibility for cut-free premises by strong induction on Lambek's degree, cut elimination as a corollary, `derivable ↔ cut-free derivable`.
- Subformula property of cut-free derivations (Prop 2.14).
- Decidability: transparent fuel-bounded backward proof search `prove`, sound and complete with the explicit bound `S (number of connective occurrences in the sequent)`; bounded derivability predicate `derivable_b`; `derivable_dec`; computed examples by `vm_compute`.
- Curry–Howard: de Bruijn λ-terms assigned to derivations (Moortgat Def 3.2, M&R §3.3 step 2); typing in the simply typed λ-calculus over `e, t` under the homomorphism `(·)*`; the substitution lemma (untyped σ-calculus form and typed form); `term (cut d1 d2) = subst … (term d2)` by definition; `β*`-preservation of the proof term by cut admissibility and by cut elimination.
- Montague semantics: `sem : formula prim -> Type` (`np ↦ Entity`, `s ↦ Prop`, `n ↦ Entity -> Prop`, `A\B`, `B/A ↦ sem A -> sem B`), denotation of derivations, lexicon {John, every, some, man, walks, sees}, theorems: "every man walks" denotes `forall x, man x -> walks x`, "some man walks" denotes `exists x, man x /\ walks x`, "John walks" denotes `walks john`; compositionality of cut in the semantics; coherence `sem A = interp_stype (star A)`.

### Formalized — STRETCH (priority order)
1. Derived rules with semantic readings: type raising, composition, Geach, restructuring, iso/antitonicity, application (Lambek §7 (f)–(n); M&R p. 30; Moortgat Prop 2.18).
2. Object-position quantifier and the two scope readings of "every man sees some man" (M&R Ex 3.5), exercising `/R` on a hypothetical `np`.
3. Models: pre-ordered residuated semigroups, soundness (Prop 2.20), Z-count model → count invariant (Prop 2.6) and `~ derivable [np] s`; free-semigroup completeness for product-free L (Prop 2.22).
4. Linearity and β-normality of proof terms (Moortgat Def 3.3, Prop 3.4, p. 21).
5. Semantic invariance of cut elimination (`denote (cut_elim d) ≈ denote d` under `ext_eq`); uniqueness of the reading of "every man walks" over all its sequent proofs.
6. Type-valued certified search returning derivations.
7. Product `•` (two constructors, pairs/`let` in terms, extra cut cases).

### Deliberately out
Empty antecedents (L∅, M&R §2.5); natural deduction, normalization and SC/ND equivalence (M&R §§2.2, 2.4, 2.6; only the sequent calculus is the object of study); Lambek's arrow axiomatics (a)–(e) and the §8 equivalence proof (they need `•` to state (b)); interpolation (§2.10); Pentus/context-freeness (§2.11, excluded by the brief); NL/multimodal calculi, proof nets, linear logic (motivation only); intensionality and DRT (§§3.6–3.7); Lindenbaum-quotient completeness (Prop 2.21: needs quotients and `•`); confluence/strong normalization of the λ-calculus (never needed; only `β*` and, for stretch 4, normality of cut-free terms — uniqueness of normal forms is not claimed); efficiency of proof search / spurious ambiguity (§2.8 remarks).

---

## 2. Representation decisions (with justification)

| Decision | Choice | Why |
|---|---|---|
| Primitive types | `Section` variable `Atom : Type`; `Hypothesis Atom_eq_dec` used only by `prove`; instantiated by `Inductive prim := np \| n \| s` (`decide equality`, `Defined`) | Faithful to "a set P of primitive types" (M&R §2.1, Lambek §7); the metatheory never compares atoms; `Defined` so `vm_compute` runs |
| Formulas | `Inductive formula := at_ (a : Atom) \| bs (A B : formula) (* A \ B *) \| sl (B A : formula) (* B / A *)`; notations `A \ B`, `B / A` at level 40 in `lambek_scope`, declared outside the section | M&R §2.1 grammar minus `•`; a dedicated scope avoids `Nat.div`, `Z.div` and `\/` clashes |
| Antecedents | `list formula`; holes `Γ, A, Γ'` as `Γ1 ++ A :: Γ2` with explicit `Γ1 Γ2` constructor arguments | Vectors turn every `++` into a transport; explicit pieces are exactly Lambek's `U, x, V` |
| Non-emptiness | `Prop` side condition `Γ <> []` on `\R`, `/R` only, placed after the derivation premise; global non-emptiness is a theorem | Where M&R/Lambek put it; no non-empty-list type; `Deriv_rect` orders hypotheses conveniently |
| Derivations | One family `Deriv : bool -> list formula -> formula -> Type`, flag = "cut allowed"; constructors polymorphic in the flag except `d_cut` which requires `true`; `weaken_flag`; `derivable Γ A := inhabited (Deriv true Γ A)`, `cf_derivable Γ A := inhabited (Deriv false Γ A)` | Proof objects are needed for terms, denotations and the output of cut elimination; the flag avoids duplicating `term`/`denote`/subformula lemmas over two families; `inhabited` restores the sources' relation `Γ ⊢ A` |
| Constructor indices | Direct (`Deriv b (Γ1 ++ Δ ++ (A \ B) :: Γ2) C`), not Fording equations | `term`/`denote` are plain dependent matches; inversion uses `remember … as Θ; destruct d` (verified axiom-free) |
| Cut measure | Lambek's single natural number `conn_ctx Γ + conn_ctx Δ1 + conn_ctx Δ2 + conn A + conn C` (Lambek §9; Moortgat p. 12 eq. (9) uses the same); strong induction on `n` with `measure < n`, into `Type` | Every permutation and principal case strictly decreases it; one induction instead of Design B's triple nested structural induction; no height function; M&R's (degree, depth) is only needed for their "remove one cut of smallest depth" formulation (documented, not used) |
| Admissibility vs elimination | `cut_adm` on cut-free premises (Lambek's own formulation), then `cut_elim` by structural induction | Keeps the big case analysis in one theorem; the elimination corollary is 30 lines |
| λ-terms | Untyped de Bruijn `tm := var nat \| app \| lam`; the antecedent *is* the environment (hypothesis at position `i` = `var i`); parallel substitution `subst : (nat -> tm) -> tm -> tm`, renaming `ren`, `up`; every cut-like operation is an instance of `cut_subst k m t` ("replace variable `k` by `t` placed at positions `k..k+m-1`, shift the rest") | No native binders; a σ-calculus keeps all index arithmetic in a handful of generic lemmas; `\L`, `/L` and `cut` are all `subst (cut_subst …)`, so "cut is substitution" holds by definition (Moortgat Def 3.2, p. 13 eq. (10)) |
| `/R` term | `lam (ren (rot (length Γ)) t)` with `rot n : n ↦ 0, i < n ↦ i + 1` | The directional calculus has no native λ-counterpart; the ordered calculus is collapsed onto the ordinary one exactly as M&R do ("reading a\b and b/a as a→b", p. 74) |
| Typing | Church-style relation `typed : list stype -> tm -> stype -> Prop`, `stype := e \| t \| arr`; `star : (Atom -> stype) -> formula -> stype`, instantiated at `prim` | M&R §3.2.1/§3.3; a relation rather than intrinsically typed terms so substitution and β need no transports |
| Semantics | `sem : formula prim -> Type` by recursion; `env : list formula -> Type` nested products; `env_split`/`env_app`/`env_snoc`; `denote : Deriv b Γ A -> env Γ -> sem A` by dependent match; `ext_eq A : sem A -> sem A -> Prop` (`iff` at `s`, `eq` at `np`, pointwise at `n` and at function types) | M&R's four-step algorithm executed inside Coq (lexical meanings are Coq values; "substitute then β-reduce" is definitional equality); `ext_eq` states semantic equalities without funext (Design B) |
| Lexicon and model | Section variables `Entity : Type`, `john : Entity`, `man walks : Entity -> Prop`, `sees : Entity -> Entity -> Prop`; lexical meanings are closed `Definition`s | Fragment theorems close by `reflexivity` (verified in the probe) and are universally quantified over the model after `End Section`; `Entity : Type`, never `Set` |
| Models (stretch) | `Record RSG` with carrier, `op`, `ldiv`, `rdiv`, `le` a **preorder**, `eqv` an equivalence respected by `le`, `op_assoc` up to `eqv`, residuation laws `rsg_l/rsg_r`; contexts interpreted in the option-monoid lift (`None` = formal unit); powerset model with sets as `W -> Prop`; Z-count model on `Atom -> Z` | Antisymmetry is never used in Props 2.19–2.20 and the powerset order is antisymmetric only up to predicate extensionality; the unit lift is M&R's own remark (p. 44); the abelianised free group is all the count invariant needs (Design B) |
| Decidability | `prove : nat -> list formula -> formula -> bool`, transparent, exhaustive over hole positions and neighbouring splits; bound `S (conn_ctx Γ + conn A)` proven as a theorem | No `Program`/`Function`/Equations; Lambek's "every upward step eliminates a connective" *is* the bound |
| Classical/constructive | Fully constructive, no axioms; `Print Assumptions` closed on every headline theorem; `sem s = Prop` (proof-irrelevant, not `bool`) | Project convention; Montague's `{0,1}` is documented as an artifact |
| `Qed`/`Defined` | `cut_adm`, `cut_elim` opaque (`Qed`) with all needed facts inside the sigma type; `prove`, `splits`, `holes`, `formula_eq_dec`, `prim_eq_dec` transparent | Cut-elimination proof terms are huge and never executed; search must compute |

---

## 3. Definitions (numbered, with source)

**Part 1 — Syntax**
1. `Atom : Type` (section variable), `Atom_eq_dec : forall a b : Atom, {a = b} + {a <> b}` (hypothesis). — Lambek §2 p. 155; M&R §2.1 p. 23.
2. `formula := at_ Atom | bs formula formula | sl formula formula`; notations `A \ B := bs A B`, `B / A := sl B A` in `lambek_scope`; `formula_eq_dec` (`decide equality`, `Defined`). — M&R §2.1 p. 24; Lambek §2 p. 155.
3. `ctx := list formula`; `conn : formula -> nat` (number of connective occurrences), `conn_ctx := fold_right (fun A n => conn A + n) 0`; `conn_ctx_app`; `conn_seq Γ A := conn_ctx Γ + conn A`. — Lambek §9 p. 167 (`d(x)`, `d(x1,…,xn)`); Moortgat p. 12.
4. `subformula : formula -> formula -> Prop`, reflexive–transitive closure of "direct subformula" (`A`, `B` direct in `A \ B` and `B / A`). — M&R §2.3 p. 29, Prop 2.14 p. 40.

**Part 2 — Calculus**
5. `Deriv : bool -> ctx -> formula -> Type`:
   - `d_ax : Deriv b [A] A`
   - `d_bsR : Deriv b (A :: Γ) B -> Γ <> [] -> Deriv b Γ (A \ B)`
   - `d_slR : Deriv b (Γ ++ [A]) B -> Γ <> [] -> Deriv b Γ (B / A)`
   - `d_bsL : Deriv b Δ A -> Deriv b (Γ1 ++ B :: Γ2) C -> Deriv b (Γ1 ++ Δ ++ (A \ B) :: Γ2) C`
   - `d_slL : Deriv b Δ A -> Deriv b (Γ1 ++ B :: Γ2) C -> Deriv b (Γ1 ++ (B / A) :: Δ ++ Γ2) C`
   - `d_cut : Deriv true Γ A -> Deriv true (Δ1 ++ A :: Δ2) C -> Deriv true (Δ1 ++ Γ ++ Δ2) C`
   — M&R Fig. 2.2 p. 29 (`\h, /h, \i, /i, cut, axiom`); Lambek §8 rules (1),(2),(2′),(3),(3′) p. 165, cut (6) p. 166; Moortgat Def 2.13 p. 12.
6. `derivable Γ A := inhabited (Deriv true Γ A)`; `cf_derivable Γ A := inhabited (Deriv false Γ A)`; `weaken_flag : Deriv false Γ A -> Deriv true Γ A`. — the relation `Γ ⊢ A` of M&R §2.1.
7. `sequents : Deriv b Γ A -> list (ctx * formula)` (every sequent of the derivation, end-sequent included). — needed for M&R Prop 2.14.
8. `cut_measure Γ Δ1 Δ2 A C := conn_ctx Γ + conn_ctx Δ1 + conn_ctx Δ2 + conn A + conn C`. — Lambek §9 p. 167; Moortgat p. 12 eq. (9).
9. Type-valued list surgery (all in `Type`, none needs decidable equality):
   - `split_app_cons_T : l1 ++ x :: l2 = m1 ++ y :: m2 -> {k & m1 = l1 ++ x :: k /\ l2 = k ++ y :: m2} + {x = y /\ l1 = m1 /\ l2 = m2} + {k & l1 = m1 ++ y :: k /\ m2 = k ++ x :: l2}`
   - `split_app_app_T : l1 ++ l2 = m1 ++ m2 -> {k & m1 = l1 ++ k /\ l2 = k ++ m2} + {k & l1 = m1 ++ k /\ m2 = k ++ l2}`
   - `split_hole_bs_T : Δ1 ++ X :: Δ2 = Γ1 ++ Δ ++ Y :: Γ2 -> (X in Γ1) + (X in Δ) + (X = Y ∧ Δ1 = Γ1 ++ Δ ∧ Δ2 = Γ2) + (X in Γ2)` and `split_hole_sl_T` for `Γ1 ++ Y :: Δ ++ Γ2`, each branch returning the witnesses as explicit list equations
   - `nonempty_app_l/r`, `app_not_nil`.
   — Lambek §9 "seven cases which need not be mutually exclusive"; M&R pp. 41–42 (position of the cut formula).
10. `pos_count`, `neg_count : Atom -> formula -> nat` and sequent versions (STRETCH 3; alternatively derived from the Z-count model). — M&R Def 2.4 p. 30.

**Part 3 — λ-terms**
11. `tm := var nat | app tm tm | lam tm`; `ren : (nat -> nat) -> tm -> tm`; `subst : (nat -> tm) -> tm -> tm`; `up σ := scons (var 0) (fun i => ren S (σ i))`; `ids`, `scons`; `shift k := ren (fun j => j + k)`; `rot n : nat -> nat` (`n ↦ 0`, `i < n ↦ S i`, `i > n ↦ i`); `cut_subst k m t : nat -> tm := fun i => if i <? k then var i else if i =? k then shift k t else var (i + m - 1)`. — M&R §3.2.1 pp. 67–68; Moortgat Def 3.1 (implicational part).
12. `beta : tm -> tm -> Prop` (compatible closure of `app (lam t) u ~> subst (scons u ids) t`), `beta_star` (reflexive–transitive closure). — M&R p. 68; Moortgat Def 3.5 (E1) p. 21.
13. `stype := e | t | arr stype stype`; `star (v : Atom -> stype) : formula -> stype` with `(A \ B)* = (B / A)* = arr A* B*`; at `prim`: `np ↦ e`, `s ↦ t`, `n ↦ arr e t`. — M&R §3.3 p. 74; Retoré 2005 §2.14.
14. `typed : list stype -> tm -> stype -> Prop` (`var i` when `nth_error E i = Some T`; `app`; `lam` extends the environment at position 0). — M&R §3.2.1 p. 67.
15. `linear : tm -> Prop` (every free variable occurs exactly once; every `lam` binds exactly one occurrence), `normal : tm -> Prop` (no β-redex) (STRETCH 4). — Moortgat Def 3.3 p. 20; p. 21.

**Part 4 — Curry–Howard**
16. `term : Deriv b Γ A -> tm`:
   - `d_ax ↦ var 0`
   - `d_bsR d _ ↦ lam (term d)`
   - `d_slR d _ ↦ lam (ren (rot (length Γ)) (term d))`
   - `d_bsL d1 d2 ↦ subst (cut_subst (length Γ1) (S (length Δ)) (app (var (length Δ)) (term d1))) (term d2)`
   - `d_slL d1 d2 ↦ subst (cut_subst (length Γ1) (S (length Δ)) (app (var 0) (shift 1 (term d1)))) (term d2)`
   - `d_cut d1 d2 ↦ subst (cut_subst (length Δ1) (length Γ) (term d1)) (term d2)`
   — Moortgat Def 3.2 p. 20 (`Ax x`, `Cut u[t/x]`, `→L u[y(t)/x]`, `→R λx.t`); M&R §3.3 step 2 p. 75.

**Part 7 — Decidability**
17. `splits : list X -> list (list X * list X)` (all `(l1, l2)` with `l = l1 ++ l2`), `splits_spec`; `holes : list X -> list (list X * X * list X)` (all `(Γ1, F, Γ2)` with `l = Γ1 ++ F :: Γ2`), `holes_spec`; `prove : nat -> ctx -> formula -> bool`: fuel `0 ↦ false`; fuel `S n`: axiom test `Γ = [A]` via `formula_eq_dec` (list version), `||` `\R`/`/R` on the succedent when `Γ <> []`, `||` for every hole `(Γ1, A' \ B, Γ2)` and every split `(Γ1', Δ)` of `Γ1`: `prove n Δ A' && prove n (Γ1' ++ B :: Γ2) A`, `||` symmetrically for `B / A'` with splits `(Δ, Γ2')` of `Γ2` — combined with `existsb`. `bound Γ A := S (conn_seq Γ A)`; `derivable_b Γ A : bool := prove (bound Γ A) Γ A`. — Lambek §8 p. 167 ("working from the bottom up, using Rules (1) to (5), but not (6)"); M&R Prop 2.18; Moortgat p. 13.

**Part 8 — Semantics**
18. `prim := np | n | s`, `prim_eq_dec` (`Defined`); `NP N S : formula prim`; `star_prim`. — M&R §3.3 p. 74; Lambek §2.
19. Section `Montague` with `Variable Entity : Type`: `sem : formula prim -> Type` (`np ↦ Entity`, `s ↦ Prop`, `n ↦ Entity -> Prop`, `A \ B ↦ sem A -> sem B`, `B / A ↦ sem A -> sem B`); `interp_stype : stype -> Type` (`e ↦ Entity`, `t ↦ Prop`); `env : ctx -> Type` (`[] ↦ unit`, `A :: Γ ↦ sem A * env Γ`); `env_app`, `env_split Γ1 : env (Γ1 ++ Γ2) -> env Γ1 * env Γ2` (Fixpoint on `Γ1` returning a pair), `env_snoc : env Γ -> sem A -> env (Γ ++ [A])`; `ext_eq`, `ext_eq_ctx`. — M&R §3.3 p. 74; Moortgat (13) p. 20 (`D_{A→B} = D_B^{D_A}`); Lambek p. 159.
20. `denote : Deriv b Γ A -> env Γ -> sem A`: `ax ↦ fst`; `\R ↦ fun ρ a => denote d (a, ρ)`; `/R ↦ fun ρ a => denote d (env_snoc ρ a)`; `\L`: split `ρ` into `(ρ1, (ρΔ, (f, ρ2)))`, continue in `d2` with `env_app ρ1 (f (denote d1 ρΔ), ρ2)`; `/L` symmetric; `cut`: split `ρ` into `(ρ1, (ρΓ, ρ2))`, continue with `env_app ρ1 (denote d1 ρΓ, ρ2)`. — M&R §3.3 steps 1–4 p. 75; Moortgat Def 3.2 read in the frame (13).
21. Lexicon (variables `john : Entity`, `man walks : Entity -> Prop`, `sees : Entity -> Entity -> Prop`): `John : NP ↦ john`; `every_sem : sem ((S / (NP \ S)) / N) := fun P Q => forall x, P x -> Q x`; `some_sem := fun P Q => exists x, P x /\ Q x`; `man : N ↦ man`; `walks : NP \ S ↦ walks`; `sees : (NP \ S) / NP ↦ fun o s => sees s o`; STRETCH object determiners `((S / NP) \ S) / N` with the same terms. — M&R Ex 3.5 p. 81 (`every`, `a`, `ate`), Ex 3.2 p. 76 (`some`); Lambek Table I p. 157 (`works : n\s`, `likes : n\s/n`); M&R p. 75 ("Pierre").
22. Concrete derivations: `d_john_walks : Deriv false [NP; NP \ S] S`; `d_every_man_walks`, `d_some_man_walks : Deriv false [(S / (NP \ S)) / N; N; NP \ S] S` (`/L` with `Γ1 = []`, `Δ = [N]` over `/L` with `Δ = [NP \ S]` over axioms); `d_type_raise : Deriv false [NP] (S / (NP \ S))`; `d_compose : Deriv false [A / B; B / C] (A / C)`; STRETCH `d_john_sees_every_man`, the two scope derivations of "every man sees some man". — M&R Ex 2.7 p. 30, p. 30 (`x ⊢ z/(x\z)`), Ex 3.5 pp. 81–84; Lambek §7 (g)–(i).

**Part 9 — Models (STRETCH 3)**
23. `Record RSG := { M; op; ldiv; rdiv; le; eqv; le_refl; le_trans; eqv_equiv; le_eqv_compat; op_assoc : forall a b c, eqv (op (op a b) c) (op a (op b c)); rsg_l : forall a b c, le (op a b) c <-> le b (ldiv a c); rsg_r : forall a b c, le (op a b) c <-> le a (rdiv c b) }`. — M&R §2.9.1 pp. 44–45 (RSG).
24. `interp (v : Atom -> M) : formula -> M`; `interp_ctx : ctx -> option M` with `oapp` (`None` unit), `ole`; `valid v Γ C := ole (interp_ctx v Γ) (Some (interp v C))`; `interp_ctx_app`, `interp_ctx_nonempty`. — M&R §2.9.1 p. 45; unit remark p. 44.
25. `pow_rsg W (· : W -> W -> W) (assoc)`: carrier `W -> Prop`, `op X Y w := exists a b, X a /\ Y b /\ w = a · b`, `ldiv X Z z := forall a, X a -> Z (a · z)`, `rdiv Z Y z := forall b, Y b -> Z (z · b)`, `le` = inclusion, `eqv` = mutual inclusion. — M&R §2.9.4 p. 47.
26. `zcount_rsg`: `M := Atom -> Z`, pointwise `+`, `ldiv a c := c - a`, `rdiv c b := c - b`, `le := eqv :=` pointwise `eq`. — Lambek §10 p. 169 (abelianised free group); M&R §2.9.2 p. 45.
27. Free semigroup model: `pow_rsg (list formula) (++)` with `[p] := fun Γ => derivable Γ p`; non-emptiness via the option lift. — M&R Prop 2.22 pp. 47–48.

---

## 4. Theorems (numbered; MUST/STRETCH; source; strategy)

**Calculus basics**
- T1 MUST `deriv_nonempty : Deriv b Γ A -> Γ <> []`. — M&R §2.5 p. 33; Lambek §8 p. 165. Induction on `d`; `app_eq_nil`; plus a `nonempty` tactic.
- T2 MUST `ax_expand : forall A, Deriv false [A] A` using atomic axioms only (with a predicate `atomic_axioms d`). — M&R Prop 2.3 p. 29 (Exercise 2.3); Moortgat Ex 3.7 (η-expansion). Induction on `A`: `\R` over `\L` with `Δ = [A]`, `Γ1 = []`.
- T3 MUST `weaken_flag`; `sequents_end : In (Γ, A) (sequents d)`; `sequents_premises` (each premise's sequents are included).

**Cut admissibility / elimination — headline**
- T4 MUST `cut_adm : forall n Γ A Δ1 Δ2 C (d1 : Deriv false Γ A) (d2 : Deriv false (Δ1 ++ A :: Δ2) C), cut_measure Γ Δ1 Δ2 A C < n -> { d : Deriv false (Δ1 ++ Γ ++ Δ2) C | beta_star (subst (cut_subst (length Δ1) (length Γ) (term d1)) (term d2)) (term d) }`. — Lambek §9 pp. 167–169 (Cases 1–4, 6, 7; Case 5 is the product); M&R §2.7 pp. 40–43, Thm 2.17; Moortgat Prop 2.14 (cases 1–3), Ex 3.6 (principal cut = β). Strategy: strong induction on `n`; **`destruct d1` first**, then `remember (Δ1 ++ A :: Δ2) as Θ; destruct d2`; Def. 9 lemmas locate the cut formula relative to the principal formula. Case table (documented in a comment inside the proof):
  - axiom left (Lambek Case 1): `Γ = [A]`, result `d2`; term equal by `subst_cut_var` (`cut_subst k 1 (var 0)` is the identity);
  - axiom right (Lambek Case 2): `Δ1 = Δ2 = []`, result `d1`; term equal by `subst_id`;
  - left permutation, `d1` ends in `\L`/`/L` (Lambek Case 3): cut `d2` into the right premise of the left rule (measure drops by `conn Δ + conn A + 1`), re-apply the left rule below (goal index rewritten with `app_assoc`/`app_comm_cons` before `refine`); term: `cut_subst` commutation `_gt` + `subst_ext`;
  - right permutation, `d2` ends in `\R`/`/R` (Lambek Case 4): cut into the premise; side condition from T1 + `nonempty_app`; term: `cut_subst_up` (cut under `lam`) and `cut_subst_rot` for `/R`;
  - right permutation, `d2` ends in `\L`/`/L` with the cut formula in `Γ1`, inside `Δ` (cut into `d2`'s *left* premise), or in `Γ2` (Lambek Case 4; three sub-cases per rule); term: `cut_subst` commutation `_lt`/`_gt` and `cut_subst_shift`; the middle branch of `split_hole_*_T` with a *mismatched* connective is closed by `discriminate`;
  - principal `\` and `/` (Lambek Cases 6–7; M&R case 4; Moortgat Ex 3.6): `d1 = d_bsR e`, `d2 = d_bsL f1 f2` with `Δ1 = Γ1 ++ Δ`, `Δ2 = Γ2`; first cut `f1` into `e` at position 0 (on `A`), then the result into `f2` at `length Γ1` (on `B`); both of smaller measure; term: one `beta` step (`app (lam te) tf1 ~> subst (scons tf1 ids) te`, which is `subst (cut_subst 0 (length Δ) tf1) te`) followed by the two IH `β*`s composed via `subst_beta_star`.
  Term equations are discharged by the generic lemmas of T7 + `subst_ext` + `lia`; no index arithmetic inside cases. Difficulty: very hard, ~900–1200 lines; the riskiest item. Validate the case analysis first without the term clause (`cut_adm_nt`), then add the `β*` component. **Fallback** if the `β*` clause stalls in the permutation cases: keep `cut_adm_nt` as MUST, prove the `β*` clause for the axiom and principal cases as separate lemmas, and document the downgrade; T5/T11/T15 remain stated relative to `cut_adm_nt`.
- T5 MUST `cut_elim : forall d : Deriv true Γ A, { d' : Deriv false Γ A | beta_star (term d) (term d') }`; corollaries `derivable_iff_cf : derivable Γ A <-> cf_derivable Γ A`. — M&R Thm 2.17 p. 43; Lambek §9 ("this will establish Gentzen's theorem"). Structural induction on `d`; cut case: IHs then T4 with `n := S (cut_measure …)`; compose `β*` via `subst_beta_star` and `beta_star_subst` (β* is a congruence in both arguments of `subst`).
- T6 MUST `subformula_property : forall d : Deriv false Γ C, In (Γ', C') (sequents d) -> In F (C' :: Γ') -> exists G, In G (C :: Γ) /\ subformula F G`. — M&R Prop 2.14 p. 40, Thm 2.17; Moortgat p. 13. Rule-local lemma "every premise formula is a subformula of some conclusion formula" (the source's proof), induction on `d`, transitivity of `subformula`.

**Curry–Howard**
- T7 MUST σ-calculus lemmas: `ren_ren`, `subst_ren`, `ren_subst`, `subst_subst`, `subst_ext`, `subst_id`, `subst_cut_var`, `cut_subst_comp_lt`/`_gt` (two cuts at different positions commute: `subst (cut_subst k m t) (subst (cut_subst k' m' u) v) = subst (cut_subst … u') (subst (cut_subst … t) v)` with the shifted indices), `cut_subst_shift` (cut into a term placed under `shift`), `cut_subst_up` (cut under `lam`), `cut_subst_rot` (cut under `/R`'s rotation), `subst_beta_star : beta_star u u' -> beta_star (subst σ u) (subst σ u')`, `beta_star_subst : (forall i, beta_star (σ i) (σ' i)) -> beta_star (subst σ t) (subst σ' t)`, `beta_subst` (a β step commutes with substitution). Standard; each by induction on the term with pointwise arithmetic `destruct (lt_eq_lt_dec i k); lia`.
- T8 MUST substitution lemma (typed): `typed_ren : typed E t T -> (forall i T', nth_error E i = Some T' -> nth_error E' (ρ i) = Some T') -> typed E' (ren ρ t) T`; `typed_cut_subst : typed E1 t T -> typed (E2 ++ T :: E3) u U -> typed (E2 ++ E1 ++ E3) (subst (cut_subst (length E2) (length E1) t) u) U`. — Moortgat Def 3.2 ("Cut corresponds to substitution"); standard STLC. Induction on the typing derivation with generalised environment; `nth_error_app1/2`.
- T9 MUST `term_typed : forall d : Deriv b Γ A, typed (map star Γ) (term d) (star A)`. — M&R §3.3 steps 1–2 p. 75; Moortgat Prop 3.4. Induction on `d`; `\L`, `/L`, `cut` via T8; `/R` via `typed_ren` with `rot`.
- T10 MUST `term_cut_eq : term (d_cut d1 d2) = subst (cut_subst (length Δ1) (length Γ) (term d1)) (term d2)` and `term_bsL_eq`, `term_slL_eq` (left rules are compiled cuts, Moortgat p. 13 eq. (10)). By `reflexivity`; stated because the brief names "the substitution lemma for cut".
- T11 MUST `cut_adm_beta` (second component of T4) and `cut_elim_beta : beta_star (term d) (term (proj1_sig (cut_elim d)))` (second component of T5). — Moortgat Def 3.5/Ex 3.6 p. 21 ("the principal Cut Elimination step replaces a redex by its contractum"); M&R p. 75 step 4.
- T12 STRETCH 4 `term_linear : linear (term d)`; `cutfree_term_normal : forall d : Deriv false Γ A, normal (term d)`; corollary: `term (cut_elim d)` is a β-normal form reachable from `term d`. — Moortgat Def 3.3/Prop 3.4 p. 20, p. 21. Induction; substituting a variable-headed term for a variable preserves normality.

**Decidability — headline**
- T13 MUST `prove_sound : prove n Γ A = true -> cf_derivable Γ A`. — Lambek §8 p. 167; M&R Prop 2.18. Induction on `n`; `orb_true_iff`, `existsb_exists`, `andb_true_iff`, `splits_spec`, `holes_spec`; derivations built inside `inhabited`.
- T14 MUST `prove_complete : forall d : Deriv false Γ A, forall n, conn_seq Γ A < n -> prove n Γ A = true`. — Lambek §8 "every upward step eliminates an occurrence of one of the connectives". Induction on `d`; each premise has connective count at most one less (`conn_ctx_app`, `lia`); witnesses via `splits_spec`/`holes_spec` and `existsb_exists`. Proved for every `n` above the bound so the axiom case needs no fuel monotonicity.
- T15 MUST `derivable_b_spec : derivable_b Γ A = true <-> derivable Γ A` (bounded derivability predicate), `derivable_dec : forall Γ A, {derivable Γ A} + {~ derivable Γ A}`, `cf_derivable_dec`. — Lambek §8 p. 155/167 ("the decision problem … is solved affirmatively"); M&R Prop 2.18; Moortgat p. 13. Case on `prove (bound Γ A) Γ A`; positive branch T13 + `weaken_flag`; negative branch: `derivable → T5 → T14 → true`, contradiction.
- T16 MUST computed examples (`vm_compute`): `prove 4 [NP; NP \ S] S = true`; `prove 4 [NP \ S; NP] S = false`; `prove 8 [(S / (NP \ S)) / N; N; NP \ S] S = true`; `prove 8 [NP] (S / (NP \ S)) = true`; `prove 8 [S / (N \ S)] N = false` (M&R p. 45: the free-group/count check cannot separate this); `prove 8 [(N / N) / (N / N); NP / N; N] NP = false` ("a very book" needs the empty sequence, M&R §2.5 p. 33). Keep sequents ≤ 5 formulas, fuel ≤ 10.

**Montague fragment — headline**
- T17 MUST `john_walks_sem : denote d_john_walks (john, (walks, tt)) = walks john`; `every_man_walks_sem : denote d_every_man_walks (every_sem, (man, (walks, tt))) = (forall x, man x -> walks x)`; `some_man_walks_sem : denote d_some_man_walks (some_sem, (man, (walks, tt))) = (exists x, man x /\ walks x)`. — M&R Ex 3.5 p. 84 (`∀u child(u) ⇒ …`), Ex 3.2 pp. 76–77, §3.3 p. 75 steps 1–4; Lambek p. 159. By `reflexivity` (verified in the probe for `every`).
- T18 MUST `denote_cut : denote (d_cut d1 d2) ρ = let (ρ1, ρ') := env_split Δ1 ρ in let (ρΓ, ρ2) := env_split Γ ρ' in denote d2 (env_app ρ1 (denote d1 ρΓ, ρ2))` and the `denote_bsL`/`denote_slL` analogues — compositionality of cut in the semantics (M&R p. 75 step 3 "replace each variable xi by τi"; Moortgat Def 3.2 `u[t/x]`). `reflexivity` after `cbn`.
- T19 MUST `sem_star : forall A, sem A = interp_stype (star_prim A)` — the deep typing and the shallow semantics agree. Induction on `A`; `reflexivity` per case. Ties T9 to `denote`.
- T20 STRETCH 1 derived rules with denotations: `type_raise_l : Deriv b Γ A -> Deriv b Γ (B / (A \ B))`, `type_raise_r : … -> Deriv b Γ ((B / A) \ B)`, `compose : Deriv b [A / B; B / C] (A / C)`, `geach : Deriv b [A / B] ((A / C) / (B / C))`, `restructuring : Deriv b [(A \ B) / C] (A \ (B / C))` and converse, `application : Deriv b [A / B; B] A`, `mono_iso : derivable [A] B -> derivable [A / C] (B / C)`, `mono_anti : derivable [A] B -> derivable [C / B] (C / A)` (via one cut, illustrating T4/T5); `type_raise_sem : denote d_type_raise (john, tt) = fun P => P john` (`reflexivity`, verified), `compose_sem` with `ext_eq` (`fun f g x => f (g x)`). — Lambek §7 (f)–(n) pp. 163–164, §6 (II)–(IV); M&R p. 30 (`x ⊢ z/(x\z)`), p. 75 ("Pierre ↦ λP (P Pierre)"); Moortgat Prop 2.18 (1),(4)–(10) p. 15.
- T21 STRETCH 2 `john_sees_every_man_sem = (forall x, man x -> sees john x)` (object determiner `((S / NP) \ S) / N`, `/R` on a hypothetical `np` — M&R p. 30 "this hypothetical np corresponds to a trace"); two derivations of "every man sees some man" with readings `forall u, man u -> exists x, man x /\ sees u x` and `exists x, man x /\ forall u, man u -> sees u x`. — M&R Ex 3.5 pp. 81–84. Explicit derivations; `reflexivity`/`cbn` (closed terms).

**Models (STRETCH 3)**
- T22 `rsg_mono_l/r/both` (M&R Prop 2.19 p. 45, exactly the source's proof from reflexivity + (RSG) + transitivity); `ole_mono_ctx`; `pow_is_rsg` (§2.9.4 p. 47, `firstorder` with witnesses); `zcount_is_rsg` (`lia` pointwise).
- T23 `rsg_sound : Deriv b Γ A -> forall (R : RSG) v, valid v Γ A` (M&R Prop 2.20 p. 46, proved there for ND; here by induction on `d`; the `\L` case: `[Δ] < [A]` ⇒ `[Δ]∘[A\B] < [A]∘([A]\\[B]) < [B]` by T22 and (RSG), then `ole_mono_ctx`).
- T24 `count_invariant : Deriv b Γ A -> forall p, count_ctx p Γ = count p A` as the Z-count instance of T23 (M&R Prop 2.6 p. 30; Lambek §10); corollaries `~ derivable [NP] S`, `~ derivable [S] NP`. (`s/(n\s) ⊬ n` is *not* obtainable this way — M&R p. 45 — hence T16.)
- T25 `free_semigroup_complete : (forall v, valid_free v Γ A) -> derivable Γ A` for product-free L (M&R Prop 2.22 pp. 47–48): truth lemma `[F] = Ctx(F)` by induction on `F` (`Ctx(G\H) ⊆ [G\H]` uses `\L` + cut, the converse uses `G ∈ Ctx(G)` and `\R`), then `Ai ∈ [Ai]`.

**Semantic invariance (STRETCH 5)**
- T26 `denote_cut_elim : forall ρ, ext_eq A (denote (proj1_sig (cut_elim d)) ρ) (denote d ρ)`. Route (a): a typed evaluator `eval : typed E t T -> env' E -> interp_stype T` (proof-relevant typing family), `beta_sound` (β preserves `eval` up to `ext_eq`), coherence `denote d ≈ eval (term_typed d)` (uses T19), then T11; route (b): re-run the T4 case analysis with the `env_split/env_app` algebra (Design B's plan). Choose (a) unless the typing family causes transport trouble.
- T27 `every_man_walks_unique : forall d : Deriv false [(S / (NP \ S)) / N; N; NP \ S] S, denote d ρ <-> (forall x, man x -> walks x)` (M&R §2.8 "bureaucratic" differences; Moortgat's Finite Reading Property). Inversion on the last rule with Def. 9 to enumerate positions.

**Certified search (STRETCH 6)**
- T28 `search : nat -> forall Γ A, option (Deriv false Γ A)` with `search_sound`, `search_complete` (a first-`Some` combinator over `holes`/`splits` instead of `existsb`; Type-valued `existsb_true_T`).

**Product (STRETCH 7)**
- T29 `•L`, `•R`, `pair`/`letpair` in `tm` with a second β-rule, extension of T4–T6, T9, T13–T15. — M&R Fig. 2.2, §2.7 `•` cases; Lambek rules (4),(5), Case 5; Moortgat Def 3.2 (◦L, ◦R).

---

## 5. Expected artifacts (tagged `(* [ARTIFACT-<class>] … *)` at the definition site; summarised in Part 10 with `Print Assumptions` for T4, T5, T6, T9, T15, T17)

- **(i) Strict positivity.** None: `formula`, `tm`, `Deriv`, `RSG` are strictly positive; `sequents`, `subformula`, `typed`, `sem`, `env` are functions/relations, not nested inductives. Recorded as "none" (defining "all sequents of `d` satisfy P" as an inductive over `Deriv` is tempting and unnecessary).
- **(ii) Universe / type–value collapse.** `sem : formula -> Type` by large elimination; `env Γ` is a computed type (lemmas go through `env_split`/`env_app`, never `rewrite` inside `env`). `s ↦ Prop`: Montague's `{0,1}` (Lambek p. 159 "truth values") becomes proof-irrelevant `Prop`; equality of readings is definitional or `ext_eq`/`iff`, never decidable; "true in the model" is not a boolean. `Deriv` in `Type` vs the sources' relation `⊢`: `derivable := inhabited`. `n ↦ Entity -> Prop`: "a subset of the set of entities" as a predicate. Linearity of proof terms is invisible in `denote` and visible only syntactically (T12). `Entity : Type`, not `Set`.
- **(iii) Computational opacity.** `cut_adm`/`cut_elim` are `Qed`: the returned derivation does not compute; every downstream fact (cut-freeness by the flag, β-reachability) is carried inside the sigma type; "cut elimination preserves the term" is a theorem about the procedure, not a computed check. `prove`, `splits`, `holes`, `formula_eq_dec`, `prim_eq_dec` are transparent and run under `vm_compute`. `denote` reduces by `cbn`/`reflexivity` only on closed derivations with closed environments; open `Γ` blocks on `env_split`.
- **(iv) Missing native structure.** Holes `Γ, A, Γ'` as `Γ1 ++ A :: Γ2` plus Type-valued splitting lemmas (Def. 9) replace "by inspection of the position of the cut formula"; Lambek's "seven cases" become one branch per relative position of two holes (comment table inside T4). No non-empty-list type (side condition + T1). No native `\`/`/` symmetry: the sources prove `\` and say "`/` is symmetrical" (M&R p. 41, Lambek Case 7); in Coq both families of cases are written — a `mirror` involution was considered and rejected (it transports along `rev (map mirror …)` on a `Type` family and reverses de Bruijn positions). No binders: de Bruijn σ-calculus; the directional `/R` needs `rot`, collapsing the ordered λ-calculus onto the ordinary one as M&R do (p. 74). No quotient types: the Lindenbaum algebra (Prop 2.21) is not built; `RSG` is pre-ordered with `eqv`; completeness w.r.t. free semigroups instead. Semigroups without unit vs lists with `[]`: option-monoid lift (M&R p. 44). Free group replaced by its abelianisation `Atom -> Z` (the real free group would need reduced words). `\i` "shared between SC and ND" (M&R naming) is not represented since ND is out.
- **(v) Decidability gap.** Atom equality is an explicit hypothesis used only by `prove` (the sources assume a finite `P`); formula/list equality derived; derivability decidable by theorem (T15) with a proven bound (no `Equations`/`Program`); Prop-valued stdlib lemmas (`app_eq_app`, `existsb_exists`) cannot build `Type`-valued derivations — Type-valued twins (Def. 9, `existsb_true_T`) where a derivation must be built, `inhabited` where not (T13); nothing about models or `ext_eq` is decidable; `Γ <> []` proofs inside derivations are proof-irrelevant in practice (no theorem compares derivations).

---

## 6. Pitfalls

1. **Inversion on the indexed family.** `destruct`/`inversion` on `d : Deriv b (Δ1 ++ A :: Δ2) C` fails or yields `existT` equations; use `remember (Δ1 ++ A :: Δ2) as Θ eqn:E; destruct d` (verified). Never `dependent destruction`/`dependent induction` (JMeq/UIP axioms). If an `existT` equation appears, `Eqdep_dec.inj_pair2_eq_dec` with `list_eq_dec formula_eq_dec` is axiom-free.
2. **Splitting lemmas must live in `Type`.** `List.app_eq_app` is Prop and cannot build a `Deriv`. Write `split_app_cons_T`/`split_app_app_T`/`split_hole_*_T` returning `sum`/`sigT` (no decidable equality needed).
3. **Strong induction into `Type`.** `induction n` with an explicit `measure < n` hypothesis (or `Wf_nat.lt_wf_rect`); no `Function`/`Program Fixpoint`.
4. **Order of destruction in T4.** Destruct `d1` first: axiom and `\L`/`/L` on the left are handled without looking at `d2`; only when `d1` ends in `\R`/`/R` destruct `d2`. This makes the principal case arise exactly when the middle branch of `split_hole_*_T` yields `A \ B = A' \ B'` (`injection`), while a mismatched connective in that branch is `discriminate`.
5. **Non-emptiness side conditions** in every `\R`/`/R` permutation case (`Δ1 ++ Γ ++ Δ2 <> []`): derive from T1 on the left premise with `nonempty_app_l/r`; never `discriminate` on symbolic lists.
6. **de Bruijn arithmetic.** Prove the generic `cut_subst` lemmas (T7) first and never do index arithmetic inside cut-elimination cases; each generic lemma is `destruct (lt_eq_lt_dec i k); lia`. Note `cut_subst` must shift the inserted term by `k` (positions of `Γ` inside `Δ1 ++ Γ ++ Δ2`) and `var (i + m - 1)` for `i > k`.
7. **Transport across `app_assoc`.** In T4 the output context (e.g. `Δ1 ++ (Γ1 ++ Δ ++ (A \ B) :: Γ2) ++ Δ2`) must be rewritten to the constructor's shape with `app_assoc`/`app_comm_cons` **on the goal** before `refine`/`exists`; `rewrite` on a goal in `Type` is fine, but never rewrite in a hypothesis `d : Deriv …` (it produces a cast whose `term` is no longer syntactically `term d`). If a cast is unavoidable, provide `deriv_cast : Γ = Γ' -> Deriv b Γ A -> Deriv b Γ' A` with `term_deriv_cast : term (deriv_cast e d) = term d` (destruct `e`). Keep a small toolkit of list-shape lemmas. Alternatively state T4 with a universally quantified output index `forall Θ, Θ = Δ1 ++ Γ ++ Δ2 -> {d : Deriv false Θ C | …}`.
8. **`Qed` vs `Defined`.** `cut_adm` opaque with all facts in the sigma (or `Defined` + `Opaque`); `prove`, `splits`, `holes`, `formula_eq_dec`, `prim_eq_dec` transparent (`Defined`); `ltac:(discriminate)` proofs of `Γ <> []` in concrete derivations are fine because `denote`/`term` never match on them.
9. **Computed types.** `env (Γ1 ++ Γ2)` does not reduce when `Γ1` is a variable; state semantic lemmas via `env_split`/`env_app` and their inverse laws (`env_split_app`, `env_app_split`); in `denote` give the implicit `Γ2` of `env_app` explicitly (`@env_app Γ1 (B :: Γ2) …`) — unification does not see through `env [A] ≡ sem A * unit` (verified failure and fix). Define `env_split` as a `Fixpoint` returning a pair and destructure with `fst`/`snd` so `cbv` fully reduces.
10. **Notations and scopes.** Declare `lambek_scope` outside the section (notations inside a section are discarded at `End`); re-declare `A \ B`, `B / A` after the section with the atom argument implicit. `/` at level 40 coexists with `Nat.div`/`Z.div` only in the dedicated scope; keep `nat_scope`/`Z_scope` closed or use `%L`. `\` followed by `/` lexes as `\/`: always write `(A \ B)`, `(B / A)` with spaces and parentheses. Close `lambek_scope` in the Z-count module.
11. **Sections and inductives.** `Deriv` under `Variable Atom` gains `Atom` as an explicit first argument after the section: `Arguments Deriv {Atom}` and `Set Implicit Arguments` early.
12. **`existsb` proofs.** `prove_sound` targets `cf_derivable` (an `inhabited`) because `existsb_exists` is Prop; the Type-valued searcher (T28) needs a `find`-style combinator.
13. **Fuel completeness.** Prove T14 for every `n` above the bound so the axiom case needs no fuel monotonicity; `prove` recurses with `n` for both premises, whose connective count is strictly smaller.
14. **`reflexivity` on the fragment.** Works only when derivation, environment tuple and lexical meanings are closed; lexical meanings must be `Definition`s, not section `Variable`s (model constants `john`, `man`, … may be variables: they occur on both sides).
15. **Duplicated symmetric cases.** Write the `\` cases with a reusable tactic (`solve_perm_case`), then the `/` cases; do not attempt mirroring.
16. **Universe checks.** `sem` returns `Type` and mentions `Prop`; keep `Deriv` independent of `sem` (never index derivations by semantic values); `Entity : Type`.
17. **`vm_compute` blow-up.** `prove` is exponential in the sequent length; keep computed examples ≤ 5 formulas and fuel ≤ 10.
18. **Zero-axiom discipline.** `Print Assumptions` after every headline theorem; funext temptations arise exactly where `ext_eq` should be used.

---

## 7. Build order (each step compiles on its own; ✓ = commit point)

1. Part 0–1: header, scope comment, `formula`, notations, `conn`, `subformula`, `formula_eq_dec`. ✓
2. Part 2: `Deriv`, `derivable`, `weaken_flag`, T1, T2, `sequents`, T3; concrete derivations Def. 22 (syntax only). ✓
3. Part 8 (early headline): `prim`, `sem`, `interp_stype`, `env`, `env_split/app/snoc`, `ext_eq`, `denote`, lexicon, T17, T18, T19, `type_raise_sem`. ✓ (quick win; validates `denote` before the heavy proofs)
4. Part 3: `tm`, `ren`, `subst`, `cut_subst`, `beta`, `beta_star`, T7 σ-calculus lemmas; `stype`, `star`, `typed`, T8. ✓
5. Part 4: `term`, T9, T10. ✓
6. Part 6: T6 subformula property. ✓
7. Part 7: `splits`, `holes`, `prove`, T13, T14, T16 examples; `cf_derivable_dec` and `derivable_b_spec` stated for `cf_derivable` first. ✓
8. Part 5: Def. 9 splitting lemmas, `cut_measure`, T4 (first `cut_adm_nt` without the term clause to validate the case analysis, then add the `β*` component), T5, T11; upgrade T15 to `derivable`. ✓ (headline)
9. Stretch 1–2: derived rules T20, object quantifier and scope readings T21. ✓
10. Stretch 3: Part 9 models T22–T25.
11. Stretch 4–7 as budget allows (T12, T26–T29).
12. Part 10: artifact table, `Print Assumptions` audit.
