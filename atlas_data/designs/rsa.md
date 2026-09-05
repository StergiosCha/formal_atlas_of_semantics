# Design: `atlas/probabilistic/RSA.v` — the Rational Speech Act model in exact rational arithmetic

Target: `/Users/graogro/Dropbox/revisiting-formal-semantics/atlas/probabilistic/RSA.v` (create `atlas/probabilistic/`). Coq 8.20.1, stdlib only: `QArith`, `Qreduction`, `Lqa`, `List`, `Bool`, `Lia`, `Permutation`.

Judge's verdict. Design B (semantics-first) is adopted as the backbone: abstract finite utterance type with a Boolean lexicon, `Qred`-normalization, decidable definedness predicates, `field`/`ne_of_lt` proof style. Grafted from Design A: the `is_dist ⟺ defined` *iff* form of every distribution theorem, the semantic-equivalence invariance theorems (Bergen Lemmas 1–2 for all depths and arbitrary costs) and the "no M-implicature in base RSA" corollary, the speaker-to-listener lifting lemma and the α-independent scalar implicature, Permutation well-definedness, the symmetry-problem pair, the size-driven cost as a *table* rather than a syntax, and the sign-convention note on Goodman & Frank Box 1. Rejected from A: the deep-embedded utterance syntax (`UAtom/UNot/UAnd/UOr`) — no source defines RSA over a grammar (Bergen §2.1 posits alternatives case by case; G&F 2016 eq. 4 and Bergen eq. 1 take ⟦u⟧ / `L(u,w)` as given), the scope asks for "a finite set of utterances … a literal meaning ⟦u⟧ : World → bool", and every syntactic metatheorem in A is statable and provable over the abstract lexicon. Rejected from B: the pair-valued `LS` recursion (a plain `Fixpoint Ln` with `Sn (S m) := S_of (Ln m)` is simpler for induction). Corrected: A's Horn-game parameters (source: λ = 4, c = 1, 2, 5, P(FREQ) = 2/3; A's "½, ¼, 1/16 at α = 1" match nothing in the paper).

Everything numerically load-bearing below was recompiled by the judge in a probe file (`scratchpad/probe/Probe.v`, 0.85 s total): the scalar values 3/4 vs 1/4 (17/18 vs 1/18 at α = 4; 7/8 vs 1/8 at depth 3; L0 both 1/2; S1(all|w2) = 2/3), Bergen's 1/(2n+2) for n = 1..4, the symmetry pair (1/2 = 1/2 flat; 2/3 vs 1/3 with size cost), the cookie value 1/6486 with S1(SOME|6) = 1/1297, the nine-lexica Horn game at λ = 4 (L1_LU(rare|SHORT) ≈ .3129 < L1_LU(rare|long) ≈ .3836, base model equal), `vm_compute; reflexivity` closing `<` and `==` goals directly, and `field` with `ne_of_lt` side conditions.

---

## 1. Scope

### Formalized (MUST)

| Source | What is taken |
|---|---|
| Goodman & Frank 2016, pp. 819–820 eqs. (1)–(4), Box 1 eq. (II) | The canonical triple: `P_L(w|u) ∝ P_S(u|w)P(w)`; `P_S(u|w) ∝ exp(αU(u,w))`; `U = log P_Lit(w|u) (− cost)`; `P_Lit(w|u) ∝ δ_⟦u⟧(w)P(w)`. The Figure‑1 faces example (HG/G/N; "glasses"/"hat"). |
| Frank & Goodman 2012, eqs. (1)–(2), Supplement (S1)–(S4) | Bayes' rule with prior P(r_S) and normalizer "computed for all referents"; softmax with α (S1), utility = surprisal − cost D(w) (S2), uniform literal listener (S3), the size principle (S4)/(2). |
| Bergen, Levy & Goodman 2016 (S&P 9), §3.1 eqs. (8)–(11) (the o = w collapse the paper itself performs, p. 20:14), the p ↦ p/(2p+1) table (p. 20:16), §3 "contextually more specific" (p. 20:13), §3.2 symmetry, §4.1.1 Lemmas 1–2, §4.3 restrictions (i)–(ii) (p. 20:28), valid refinement / enrichment (p. 20:29) | Depth‑n recursion L_n/S_n with cost c(u) and rationality λ; semantic-equivalence invariance; the definedness restrictions. |
| Lassiter & Goodman 2017 (Synthese), §2.1 eqs. (3)–(6), §2.3–2.5 eqs. (9)–(14), §3 eqs. (15)–(20) | Probability axioms and conditioning as the content of L0; QUD answers A = worlds; the cookie scalar-implicature example with α = 4 and constant cost. |
| Goodman & Lassiter 2015, §3 eqs. (5)–(6) | The explicit multiplicative form `P(ut|val) ∝ P(ut) · P_listener(val|ut)^α` — literally the encoding adopted below; cited as its primary justification. |

Headline theorems: distribution theorems for L0, S1, L1 in *iff* form with exact definedness conditions, and at every depth n; Bayes/product-rule/uniqueness forms of L1; general informativity ordering (any positive prior) for L0 and S1, strict and non-strict; semantic-equivalence invariance for all n and its no-M-implicature corollary; the scalar implicature computed exactly, with the L0 non-derivation and the α-independence of the preference.

### STRETCH
Bergen §4.3–4.5 lexical uncertainty (distribution theorem under restrictions (i)–(ii), conservativity, the Fig. 5 three-lexicon example, the Fig. 6 Horn game with nine lexica); Bergen's closed form L_n(∀|some) = 1/(2n+2); Lassiter & Goodman §4 threshold semantics for tall/short/∅ on a finite degree grid (eqs. (21)–(23), (27)–(32)).

### Deliberately out
Reals, `exp`, `log`, continuous priors, MCMC (L&G §4.4); Bergen's observation/world distinction and expected surprisal (eqs. (3)–(4), §4.6 ignorance implicature); G&F Box 1 eqs. (III)–(IV) (speaker uncertainty, QUD relevance), uRSA joint inference over speaker types except lexica and thresholds; Bergen §5 compositional lexical uncertainty; the Church presentation (G&L 2015 §1–2); IBR/IQR equilibria; empirical fits; a Coq proof that the ℕ-exponent encoding equals the real-valued softmax (stated as a comment-level *encoding lemma*; proving it needs `Reals`).

---

## 2. Representation decisions (with justification)

1. **Worlds and utterances are abstract types with enumerations.** `Variable W U : Type`, `ws : list W`, `us : list U`. No decidable equality is needed anywhere in the theory: sums, definedness, subset relations and cardinalities are all expressed over the enumerations with `In`/`existsb`/`filter`. `NoDup` is not needed for any normalization theorem (sums are over the list; duplicates would double-count, which is *correct* for a list-indexed model) and is a hypothesis only of the cardinality/size-principle theorem. Completeness (`forall w, In w ws`) is likewise only assumed where a statement quantifies over all of `W` (T4 undefinedness, T25 permutation). Sources assume finiteness explicitly (F&G: C = {o₁…oₙ}, V = {w₁…wₘ}; Bergen: finite sums in (8)–(11); L&G: finite until §4, which is discretized).

2. **Lexicon, not syntax.** `meaning : U -> W -> bool` is Bergen's `L(u,w) ∈ {0,1}` (eq. 1), G&F's `⟦u⟧(w)`, F&G's "Boolean function on objects". A proposition is `W -> bool`; membership is `meaning u w = true` (the only membership form used); `subset_meaning u1 u2 := forall w, In w ws -> meaning u1 w = true -> meaning u2 w = true` is Bergen's "more contextually specific" (p. 20:13) and F&G's "picks out a relatively smaller section of the context"; the strict version adds a witness in ⟦u2⟧∖⟦u1⟧ (on `ws`). Word length / syntactic size enters only through the cost function (a table in examples), which is exactly how Bergen (c monotone in length) and L&G (C(u) = ⅔·length) use it.

3. **Numbers are `Q`; equality is `Qeq` (`==`), never Leibniz.** Prior `prior : W -> Q` with `prior_pos : forall w, In w ws -> 0 < prior w` and `prior_sum1 : qsum (map prior ws) == 1` (the latter is used only by `L0_tautology`, `Pset_true`, and the threshold marginals; the RSA equations themselves never need it, which the file records).

4. **The softmax encoding (file header, verbatim derivation).** G&F eq. (2)+(3)+Box 1 (II) with the minus-sign convention of every other source: `S(u|w) ∝ exp(α(log L0(w|u) − c(u))) = L0(w|u)^α · e^{−α c(u)}` for L0 > 0, and = 0 for L0 = 0 under the sources' convention `exp(α · ln 0) = 0` (L&G p. 12; Bergen p. 20:15). With **α ∈ ℕ** and the **cost weight** `costw u` standing for the positive rational `e^{−α c(u)}`, this is an exact identity: `S(u|w) ∝ qpow (L0 u w) α * costw u`. This multiplicative form is literally G&L 2015 eq. (5) with `costw = P(ut)` (the "language prior"). Only ratios of weights matter (common factors cancel), so L&G's C(u) = 4 for all u is `costw = 1`, "zero cost" is `costw = 1`, and "cheaper" = larger weight. Where sources use irrational weights, a rational surrogate is used and the theorem is explicitly about the surrogate (table in the example module header). **Sign note:** G&F Box 1 eq. (II) prints `U = log P_Lit + cost(u)`; F&G (S2), Bergen eqs. (3)/(9), L&G eq. (10) all have `− cost`; the file follows `−` and records the discrepancy. **α = 0** is total but degenerate (`qpow _ 0 = 1`, the speaker ignores truth); it is kept statable (T4b) and every truth-sensitive theorem carries `(0 < alpha)%nat`.

5. **Argument conventions.** Listeners are `U -> W -> Q` (`L u w` = P_L(w|u)), speakers are `W -> U -> Q` (`S w u` = P_S(u|w)): the conditioning argument comes first, so `L u` and `S w` *are* the distributions and `IsDist (L1 u) ws`, `IsDist (S1 w) us` read literally.

6. **Normalization is `Qred (f a / qsum (map f l))`** with `normalize_spec : normalize f l a == f a / qsum (map f l)` (`Qred_correct`). `Qred` is invisible to the theory and indispensable to computation (without it a 7-world example at α = 4 does not finish in minutes; with it the nine-lexica Horn game runs in well under a second). `qpow` results are also `Qred`-ed inside the speaker.

7. **Definedness is explicit and decidable.** Coq's `Qdiv` is total with `x/0 = 0`, so an "undefined" RSA distribution is the zero function. `consistent u := existsb (meaning u) ws` (⟦u⟧ ∩ ws ≠ ∅; Bergen restriction (i)) and `expressible w := existsb (fun u => meaning u w) us` (some true utterance for w; restriction (ii) at o = w) are `bool`, with `_iff` lemmas to `exists`. Every distribution theorem is stated as an *iff* (`IsDist … <-> consistent u = true`), which is honest precisely because the zero function fails `IsDist`.

8. **Depth recursion.** `Fixpoint Ln n := match n with 0 => L0 | S m => L_of (S_of (Ln m)) end`, `Sn n := S_of (Ln (pred n))`, so `Sn (S m) = S_of (Ln m)` definitionally, `S1 := Sn 1`, `L1 := Ln 1`. This is Bergen's indexing (S_n reasons about L_{n−1}, L_n about S_n; G&F's S1/L1 = Bergen's n = 1). All one-step lemmas are proved for a *generic* previous listener `L` satisfying the support invariant `In w ws -> (0 < L u w <-> meaning u w = true)`, so the depth-n inductions can use them.

9. **Constructive and axiom-free.** No `Classical`, no functional extensionality (extensional facts are pointwise on `In`), decidable order on `Q` (`Qlt_le_dec`), `bool` meanings, closed numeric claims by `vm_compute; reflexivity`.

10. **File layout.**
```
RSA.v
 ├─ header: encoding lemma, sign note, artifact table, hypothesis-per-theorem table
 ├─ Module QSum        qsum, qpow, normalize (+spec), algebra of finite sums
 ├─ Module Dist        IsDist, Pset, additivity
 ├─ Section RSA        parameters; L0, S_of, L_of, Ln, Sn, S1, L1; consistent/expressible
 │    ├─ literal listener (T3–T6)      ├─ speaker (T7–T9)      ├─ pragmatic listener (T10–T12)
 │    ├─ Bayes forms (T13–T16)        ├─ ordering (T17–T21)   ├─ invariance (T22–T25)
 │    └─ depth n (T26–T27)
 ├─ Module ScalarImplicature (MUST, T28–T31)
 ├─ Module Faces, Module BergenTwoWorlds, Module Cookies (MUST-lite, T32–T34)
 ├─ Module Symmetry (STRETCH-lite, T35)
 ├─ Section LexicalUncertainty + Modules Fig5, Horn (STRETCH, T36–T40)
 ├─ Module BergenClosedForm (STRETCH, T41)
 └─ Section Threshold + Module TallGrid (STRETCH, T42–T45)
```

---

## 3. Definitions (numbered, with source refs)

**QSum / Dist**
1. `qsum : list Q -> Q := fold_right Qplus 0` — the Σ of every normalizer (F&G eq. 1 "a sum … computed for all referents"; L&G eqs. (12), (14); Bergen (8)–(11)).
2. `qpow : Q -> nat -> Q` (`qpow q 0 = 1`, `qpow q (S m) = q * qpow q m`) — `p^α` (G&F α; Bergen λ; L&G α; G&L 2015 `power … alpha`). Private, not `Qpower` (Z exponent, no base-monotonicity lemmas).
3. `normalize {A} (f : A -> Q) (l : list A) (a : A) : Q := Qred (f a / qsum (map f l))`, `normalize_spec` — the "∝" of every source made explicit.
4. `IsDist {A} (f : A -> Q) (l : list A) : Prop := (forall a, In a l -> 0 <= f a) /\ qsum (map f l) == 1` — L&G eq. (3a–b) on a finite list.
5. `Pset (A : W -> bool) : Q := qsum (map (fun w => if A w then prior w else 0) ws)` — L&G `P(A)`, eq. (3); used to state L0 as conditioning (eq. (4)).

**Section RSA** — context `W U ws us meaning prior costw alpha`, hypotheses `prior_pos`, `prior_sum1`, `costw_pos : forall u, In u us -> 0 < costw u`, `alpha_pos : (0 < alpha)%nat` (each theorem lists exactly the hypotheses it uses).
6. `L0_raw u w := if meaning u w then prior w else 0`; `L0 u := normalize (L0_raw u) ws` — G&F eq. (4); Bergen (8); L&G (9)/(27); F&G (S3) in the uniform case.
7. `S_of (L : U -> W -> Q) (w : W) := normalize (fun u => Qred (qpow (L u w) alpha) * costw u) us` — G&F (2)–(3) + Box 1 (II); Bergen (9)–(10); L&G (10)–(12), (16); G&L (5); F&G (S1)–(S2), (S4).
8. `L_of (S : W -> U -> Q) (u : U) := normalize (fun w => S w u * prior w) ws` — G&F (1); Bergen (11); L&G (13)–(14); F&G (1).
9. `Ln`, `Sn`, `S1 := Sn 1`, `L1 := Ln 1` — Bergen (8)–(11) "for integers n > 0".
10. `consistent u : bool`, `expressible w : bool` + `consistent_iff : consistent u = true <-> exists w, In w ws /\ meaning u w = true`, `expressible_iff` — Bergen restrictions (i), (ii) at o = w.
11. `card u : nat := length (filter (meaning u) ws)`; `inv_card u : Q := 1 / inject_Z (Z.of_nat (card u))` — F&G `|w|` (eq. 2).
12. `subset_meaning`, `strict_subset_meaning` — Bergen p. 20:13; F&G Supp. p. 3.
13. `uniform_prior : Prop := forall w w', In w ws -> In w' ws -> prior w == prior w'`; `flat_cost : Prop := forall u u', In u us -> In u' us -> costw u == costw u'` — F&G (D constant), Bergen §3.1 (uniform, c = 0, λ = 1).
14. `PS u := qsum (map (fun w => S1 w u * prior w) ws)` — the marginal likelihood (denominator of F&G (1), L&G (14)).
15. `sem_equiv u u' : Prop := forall w, In w ws -> meaning u w = meaning u' w` — the hypothesis of Bergen Lemmas 1–2.

**Examples (concrete inductives; all parameters fixed by `Definition`)**
16. `ScalarImplicature`: `W3 := w0 | w1 | w2` (0/1/2 objects), `U3 := usome | uall | unone`, `meaning`: some ↦ {w1, w2}, all ↦ {w2}, none ↦ {w0}; `prior := 1#3`; `costw := 1`; `alpha := 1` (also α = 4 and depth 3 variants) — L&G §3 with two objects, G&L 2015 §3.1, Bergen §3.1.
17. `Faces`: `HG | G | N`, `glasses | hat`, uniform 1/3, flat cost, α = 1 — G&F 2016 Fig. 1.
18. `BergenTwoWorlds`: `wall | wsna` (∀, ∃¬∀), `usome | uall`, prior 1/2, flat cost, α = 1 — Bergen §3.1.
19. `Cookies`: `n0 … n6`, `NONE | SOME | ALL`, prior `94#100` / `1#100`, `costw := 1` (C(u) = 4 for all u), α = 4 — L&G eqs. (15)–(16).
20. `Symmetry` (STRETCH-lite): `W3` with `U4 := s | a | n | sbna` (sbna ↦ {w1}); `size : U4 -> nat` = 1, 1, 2, 3; `cost_flat := 1`, `cost_size u := qpow (1#2) (size u)` — Bergen §3.2.
21. (STRETCH) `Lex := U -> W -> bool`; `lexica : list Lex`, `PL : Lex -> Q` (positive, sums to 1); `L0_lex L := L0` with `meaning := L`; `S1_lex L := S_of (L0_lex L)`; `L1_lu u := normalize (fun w => prior w * qsum (map (fun L => PL L * S1_lex L w u) lexica)) ws` — Bergen (26)–(29) = (34)–(37); `refines (LS L : Lex) u := (forall w, In w ws -> LS u w = false -> L u w = false) /\ exists w, In w ws /\ L u w = true` — "valid refinement" (p. 20:29); `unull` with `L unull w = true` in every lexicon and the largest cost (p. 20:28, fourth approach). `Fig5`: worlds ∀/∃¬∀ uniform, `some`/`all`/`unull`, three lexica uniform 1/3, `costw some = costw all = 1`, `costw unull = 1#50` (surrogate for e^{−4} at λ = 1, c(∅) = 5), α = 1. `Horn`: `FREQ | rare` with prior 2/3, 1/3; `SHORT | long | unull`; nine lexica = all refinements of the all-true meanings of SHORT and long (each ∈ {{FREQ,rare},{FREQ},{rare}}), uniform 1/9; α = 4 with c = 1, 2, 5, i.e. weights e^{−4} : e^{−8} : e^{−20} = 1 : e^{−4} : e^{−16}, surrogate `1`, `1#50`, `1#6250000` — Bergen Fig. 6 caption.
22. (STRETCH) Threshold: `degrees : list nat` (heights as grid indices, mapped to `Q` only when compared), `ths : list nat`; `Ut := tall | short | silent`; `meaning_th (u : Ut) (θ h : nat) : bool` (`tall ↦ θ <? h`, `short ↦ h <? θ`, `silent ↦ true`) — L&G (21)–(23), ALT = {tall, short, ∅} (§2.4, §4.4); `L0_th θ u`, `S1_th θ h u` (eqs. (27)–(28) with V = θ); `pairs := list_prod degrees ths`; `L1_th u : nat*nat -> Q` (eq. (29), uniform P(θ)); marginals `margT u θ`, `margH u h` (eqs. (30)–(31) as finite sums); `PT h u := Σ_{θ<h} margT u θ` (eq. (32)).

---

## 4. Theorems (numbered; MUST/STRETCH; source; proof strategy). Difficulty E ≤ 20 lines, M 20–80, H > 80.

**Infrastructure (MUST)**
1. `qsum_nonneg`, `qsum_pos_of_mem` (all terms ≥ 0 and some listed term > 0 ⇒ sum > 0), `qsum_zero_iff` (nonneg terms: sum == 0 ⟺ every listed term == 0), `qsum_map_ext_in` (pointwise `==` on members ⇒ sums `==`), `qsum_le_in`, `qsum_scale` (Σ c·f == c·Σ f), `qsum_div` (Σ f/c == (Σ f)/c), `qsum_app`, `qsum_perm` (Permutation invariance), `qsum_indicator : qsum (map (fun w => if b w then p else 0) l) == p * inject_Z (Z.of_nat (length (filter b l)))`. Induction on the list; `lra`. E–M.
2. `qpow_nonneg`, `qpow_pos`, `qpow_zero : (0 < n)%nat -> qpow 0 n == 0`, `qpow_mono : 0 <= a -> a <= b -> qpow a n <= qpow b n`, `qpow_strict : 0 <= a -> a < b -> (0 < n)%nat -> qpow a n < qpow b n`, `qpow_Proper : Proper (Qeq ==> eq ==> Qeq) qpow`. Induction on n; `Qmult_le_compat_nonneg`/`nra`. E–M. Plus `normalize_spec`, `normalize_nonneg`, `normalize_sum : 0 < qsum (map f l) -> qsum (map (normalize f l) l) == 1`, `normalize_zero : qsum (map f l) == 0 -> normalize f l a == 0`, `normalize_ext_in`. M. `ne_of_lt : 0 < x -> ~ x == 0`. E.

**Literal listener (MUST)** — G&F (4), Bergen (8), L&G (9)
3. `L0_dist_iff : IsDist (L0 u) ws <-> consistent u = true`. (⇐) witness ⇒ `qsum (map (L0_raw u) ws) > 0` by T1; terms ≥ 0 from `prior_pos`; `normalize_sum`. (⇒) if inconsistent every raw term is 0, the sum is 0, `normalize_zero` gives the zero function, whose sum is 0 ≠ 1. M.
4. `L0_undefined : consistent u = false -> forall w, L0 u w == 0` (the exact failure mode). E. `L0_support : In w ws -> consistent u = true -> (0 < L0 u w <-> meaning u w = true)`; `L0_false : meaning u w = false -> L0 u w == 0`. E.
5. `L0_is_conditioning : L0 u w == (if meaning u w then prior w else 0) / Pset (meaning u)` (L&G (4), (9)); `L0_prior_only : In w ws -> meaning u w = true -> L0 u w * Pset (meaning u) == prior w` ("the literal listener interprets some entirely according to the prior", Bergen p. 20:15); `L0_tautology : (forall w, In w ws -> meaning u w = true) -> In w ws -> L0 u w == prior w` (uses `prior_sum1`); `Pset_true == 1`, `Pset_additive` for pointwise-disjoint A, B (L&G (3c)). E.
6. `L0_uniform_card : uniform_prior -> NoDup ws -> In w ws -> meaning u w = true -> L0 u w == inv_card u` — F&G (S3). `qsum_indicator` + `qsum` of a constant. M (the `inject_Z`/`Z.of_nat` bookkeeping).

**Speaker (MUST)** — G&F (2)–(3) + Box 1, Bergen (9)–(10), L&G (10)–(12)
7. `S1_dist_iff : (0 < alpha)%nat -> (IsDist (S1 w) us <-> expressible w = true)` (needs `In w ws`, `costw_pos`). Raw term ≥ 0 by T2; raw term > 0 ⟺ `meaning u w` (T4 support + `costw_pos` + `qpow_pos`/`qpow_zero`); normalizer > 0 ⟺ witness; then as T3. M.
8. `S1_undefined : (0 < alpha)%nat -> expressible w = false -> forall u, S1 w u == 0`; `S1_support : (0 < alpha)%nat -> In w ws -> In u us -> expressible w = true -> (0 < S1 w u <-> meaning u w = true)`; `speaker_truthful : (0 < alpha)%nat -> meaning u w = false -> S1 w u == 0` (Bergen p. 20:15 "L_n(∃¬∀|all) = 0 always"; L&G p. 12 "definitely wouldn't say SOME or ALL"). E.
9. `S1_alpha0 : alpha = 0 -> In u us -> S1 w u == normalize costw us u` — with α = 0 the speaker ignores truth; the documented reason `alpha_pos` is needed. E.

**Pragmatic listener (MUST)** — G&F (1), Bergen (11), L&G (13)–(14)
10. `L1_dist_iff : (0 < alpha)%nat -> (IsDist (L1 u) ws <-> exists w, In w ws /\ meaning u w = true /\ expressible w = true)`; corollary `L1_dist_iff_alt : (0 < alpha)%nat -> In u us -> (IsDist (L1 u) ws <-> consistent u = true)` (u ∈ us and u true at w make w expressible), i.e. **L1's definedness condition is exactly L0's** when u is among the alternatives. Same pattern as T3 via T8. M.
11. `L1_undefined : (0 < alpha)%nat -> consistent u = false -> forall w, L1 u w == 0`. E. `L1_support : (0 < alpha)%nat -> In u us -> consistent u = true -> In w ws -> (0 < L1 u w <-> meaning u w = true)` — "pragmatic strengthening never leaves the literal denotation". E.
12. `listener_false : meaning u w = false -> L1 u w == 0`. E.

**Bayes'-rule forms (MUST)** — F&G (1), L&G (14)
13. `L1_bayes : L1 u w == S1 w u * prior w / PS u` (`normalize_spec`). E.
14. `L1_product : L1 u w * PS u == S1 w u * prior w` (unconditional product rule; degenerate case is 0 == 0) and `PS_pos_iff : (0 < alpha)%nat -> (0 < PS u <-> exists w, In w ws /\ meaning u w = true /\ expressible w = true)`. E–M.
15. `L1_propto : 0 < PS u -> exists Z, 0 < Z /\ forall w, In w ws -> L1 u w * Z == S1 w u * prior w` and `L1_unique : IsDist q ws -> (exists Z, 0 < Z /\ forall w, In w ws -> q w * Z == S1 w u * prior w) -> forall w, In w ws -> q w == L1 u w` — "∝" determines the distribution (the implicit content of every ∝ in the sources). Sum both sides ⇒ Z == PS u. M.
16. `L1_odds : 0 < PS u -> In w ws -> In w' ws -> L1 u w * (S1 w' u * prior w') == L1 u w' * (S1 w u * prior w)` (posterior odds = likelihood ratio × prior odds, division-free form). E.

**Ordering / informativeness (MUST)** — Bergen §3, F&G size principle
17. `L0_more_specific : subset_meaning u1 u2 -> In w ws -> meaning u1 w = true -> L0 u2 w <= L0 u1 w` — for *any* positive prior: `Pset ⟦u1⟧ <= Pset ⟦u2⟧` by `qsum_le_in`, then `Qle_shift_div_l` / `Qmult_le_r` + `Qinv_lt_0_compat`. M. `L0_strictly_more_specific : strict_subset_meaning u1 u2 -> … -> L0 u2 w < L0 u1 w` (witness gives `Pset ⟦u1⟧ < Pset ⟦u2⟧`). M.
18. `S1_more_specific : (0 < alpha)%nat -> subset_meaning u1 u2 -> costw u2 <= costw u1 -> In u1 us -> In u2 us -> In w ws -> meaning u1 w = true -> S1 w u2 <= S1 w u1` (the requested general ordering lemma; `flat_cost` or `costw = fun _ => 1` as the zero-cost special case). Common normalizer, so it reduces to T17 + `qpow_mono` + `Qmult_le_compat_nonneg`, then `Qmult_le_r` on the common inverse normalizer. M. Strict version `S1_strictly_more_specific` under `strict_subset_meaning` and `costw u2 <= costw u1` via `qpow_strict`. M.
19. `L1_order_from_S1 : prior w == prior w' -> S1 w' u < S1 w u -> 0 < PS u -> L1 u w' < L1 u w` — lifts speaker preferences to listener posteriors under equal priors (the mechanism of L&G (17)–(20)); `Qmult_lt_compat_r`, `Qlt_shift_div_l`. E.
20. `size_principle : uniform_prior -> flat_cost -> alpha = 1 -> NoDup ws -> In w ws -> In u us -> S1 w u == (if meaning u w then inv_card u else 0) / qsum (map (fun u' => if meaning u' w then inv_card u' else 0) us)` — F&G (2)/(S4). Rewrite under `map` with `qsum_map_ext_in` using T6. M–H.
21. `S1_prefers_informative_example`: in the scalar module, `S1 w2 uall == 2#3 /\ S1 w2 usome == 1#3` (L&G p. 13 "a speaker … almost certainly won't use SOME if ALL is true"); `vm_compute`. E.

**Semantic-equivalence invariance (MUST)** — Bergen §4.1.1 Lemmas 1–2, generalized to all n and arbitrary costs
22. `L0_sem_equiv : sem_equiv u u' -> In w ws -> L0 u w == L0 u' w` (Lemma 1). `normalize_ext_in`. E.
23. `Sn_sem_equiv / Ln_sem_equiv : sem_equiv u u' -> forall n w, In w ws -> Ln n u w == Ln n u' w /\ Sn (S n) w u * costw u' == Sn (S n) w u' * costw u` (Lemma 2 with the cost factor of Bergen eq. (22)). Induction on n through generic `S_of`/`L_of` step lemmas; needs `qpow_Proper` and `normalize_ext_in`. M–H.
24. `no_M_implicature : sem_equiv u u' -> forall n w, In w ws -> Ln n u w == Ln n u' w` — the base model cannot distinguish synonymous utterances at any depth for any cost assignment (Bergen §4.1.1 "failure of RSA to derive M-implicatures"); instantiated in `Horn` as `horn_base_equal`. E (corollary of T23).
25. `Ln_perm_invariant : Permutation ws ws' -> Permutation us us' -> forall n u w, Ln n u w == Ln' n u w` — well-definedness of the list encoding (sources use sets). `qsum_perm` + induction. M.

**Depth n (MUST)** — Bergen (8)–(11) "for integers n > 0"
26. `Ln_support : (0 < alpha)%nat -> (forall w, In w ws -> expressible w = true) -> In u us -> consistent u = true -> forall n w, In w ws -> (0 < Ln n u w <-> meaning u w = true)` — the support is exactly ⟦u⟧ at every level; induction on n carrying the invariant through generic step lemmas `S_of_support`, `L_of_support` (each assuming the invariant of its input). M–H.
27. `Ln_dist : … -> forall n, IsDist (Ln n u) ws` and `Sn_dist : … -> forall n w, In w ws -> IsDist (Sn (S n) w) us` — the exact conditions are the *same* as at depth 1 (plus coverage `expressible` for all w, which is Bergen restriction (ii); the file notes that the L1 theorem needs it only at one witness). M given T26.

**Scalar implicature, exact (MUST)** — L&G §3, G&L 2015 §3.1, Bergen §3.1
28. `scalar_L1_values : L1 usome w1 == 3#4 /\ L1 usome w2 == 1#4 /\ L1 usome w0 == 0` and `scalar_implicature : L1 usome w2 < L1 usome w1` — `vm_compute; reflexivity` (verified to close `<` goals directly). E.
29. `scalar_L0_fails : L0 usome w1 == L0 usome w2` (both 1/2): the literal listener does not derive the implicature. E. `scalar_L0_values`. E.
30. `scalar_alpha4 : L1 usome w1 == 17#18 /\ L1 usome w2 == 1#18`; `scalar_depth3 : Ln 3 usome w1 == 7#8 /\ Ln 3 usome w2 == 1#8` (implicature strengthens with depth). E.
31. `scalar_implicature_any_alpha : forall alpha, (0 < alpha)%nat -> L1 usome w2 < L1 usome w1` — symbolic: S1 w1 usome == 1 (only true alternative), S1 w2 usome == q/(q+1) with q = qpow (1#2) alpha < 1, then T19 with equal priors (L&G fn. 6: the preference "does not depend on this parameter"). M.

**Other worked examples (MUST-lite; E each, `vm_compute`)**
32. `Faces`: `L0 hat HG == 1`, `L0 glasses G == L0 glasses HG`, `L1 glasses HG < L1 glasses G` (G&F 2016 p. 820).
33. `BergenTwoWorlds`: `Ln 1 usome wall == 1#4`, `Ln 2 … == 1#6`, `Ln 3 … == 1#8`, `Ln 4 … == 1#10`, and `Ln n uall wsna == 0` for n ≤ 4 (Bergen table p. 20:16).
34. `Cookies` (α = 4): `L1 SOME n0 == 0`, `S1 n6 SOME == 1#1297`, `L1 SOME n6 == 1#6486`, `L1 SOME n1 == 1297#6486`, `L1 SOME n6 < L0 SOME n6` (= 1/6). *Fidelity note in the file:* L&G eq. (20) prints ≈ .015, but the paper's own displayed formula evaluates to ≈ .0002 and the exact value is 1/6486 ≈ .00015; the qualitative claim holds and the printed figure is recorded as a slip, not silently corrected.

**STRETCH**
35. `Symmetry`: `symmetry_neutral : L1flat s w1 == L1flat s w2` (both 1/2 — the symmetry problem, Bergen §3.2) and `symmetry_broken : L1size s w1 == 2#3 /\ L1size s w2 == 1#3` with `cost_size`. E.
36. `L1_lu_dist_iff : (0 < alpha)%nat -> (forall L, In L lexica -> forall u, In u us -> consistent_in L u = true) -> (forall L w, In L lexica -> In w ws -> expressible_in L w = true) -> (IsDist (L1_lu u) ws <-> exists L w, In L lexica /\ In w ws /\ L u w = true)` — Bergen (26)–(29) under restrictions (i)–(ii). Double sum: `qsum_pos_of_mem` applied twice with the witness two levels deep. M–H.
37. `L1_lu_conservative : lexica = [meaning] -> PL meaning == 1 -> In w ws -> L1_lu u w == L1 u w` ("generalizes the previous model", Bergen p. 20:27). M.
38. `Fig5`: `L1_lu some wsna > L1_lu some wall` (three lexica, uniform, `costw unull = 1#50`, α = 1). E. `refines` facts: the three lexica are exactly the valid refinements of the base lexicon with `some` refined and `all` fixed; `refinement_support_subset`. E–M.
39. `Horn`: `horn_M_implicature : L1_lu SHORT rare < L1_lu long rare` (verified ≈ .3129 < .3836 with the surrogate weights) and `horn_base_equal : L1 SHORT rare == L1 long rare` (instance of T24). E.
40. `all_refinements (LS : Lex) : list Lex` for finite `us`/`ws` with `In L (all_refinements LS) <-> forall u, In u us -> refines LS L u` — optional. H.
41. `bergen_closed_form : forall n, Ln n usome wall == 1 # Pos.of_nat (2*n+2)` in `BergenTwoWorlds` with invariant `0 < p /\ Ln n uall wsna == 0`; the step is `p ↦ p/(2p+1)` (Bergen p. 20:16), by unfolding one step of `Ln`, `normalize_spec`, then `field` with side conditions `~ 1+p == 0`, `~ 2p+1 == 0` from `0 < p` via `ne_of_lt` (probe-verified shape). H. Corollary `bergen_strict_decrease : Ln (S n) usome wall < Ln n usome wall` ("for all p > 0, p/(2p+1) < p"). M.
42. `L1_th_dist : (exists h θ, In h degrees /\ In θ ths /\ meaning_th u θ h = true) -> IsDist (L1_th u) pairs`; `S1_th` is always defined because `silent` is true everywhere. M.
43. `margT_sum : qsum (map (margT u) ths) == 1`, `margH_sum`, `margT_spec : margT u θ == Σ_h L1_th u (h,θ)` (L&G (30)–(31) as finite sums). E–M.
44. `L1_theta_dead : (forall h, In h degrees -> (h <=? θ) = true) -> margT tall θ == 0` (tall false everywhere ⇒ S1 = 0); `L0_th_vacuous : θ below every height ⇒ L0_th θ tall == prior`. E–M.
45. `TallGrid` (7 heights, 7 thresholds, binomial prior (1,6,15,20,15,6,1)/64, α = 4, `costw tall = costw short = 1#20`, `costw silent = 1`): (a) at L0 the threshold posterior is maximal at the lowest θ (G&L 2015 Fig. 7 phenomenon); (b) at L1 `margT tall` has an interior mode above the prior mean and `margH tall`'s mode moves up (G&L Fig. 8, L&G §4.3 "sweet spot"); (c) `PT` borderline values as exact rationals (eq. (32)). `vm_compute` (fast with `Qred`). E once definitions exist.

---

## 5. Expected encoding artifacts (each gets an `(* ARTIFACT (class) *)` comment at its site and a row in the header table)

- **(i) Strict positivity.** None: the only recursion is `Ln : nat -> …` (structural on `nat`, returning functions); no inductive has a negative occurrence. Recorded in the header as a checked absence.
- **(ii) Universe / type–value collapse.** (a) The sources multiply the truth value `L(u,w) ∈ {0,1}` into a product (Bergen (2), G&F (4) `δ_⟦u⟧`); here `bool` and `if` — site `L0_raw`. (b) Bergen's (o, w) pair collapsed to w — the paper's own move (p. 20:14), cite. (c) Threshold model: the variable θ bound by `POS` (L&G (21)–(25)) becomes a *value* component of the state `(h, θ)` and a three-place `meaning_th`; the compositional structure is not represented. (d) Utterances have no syntax; `silent`/`unull` are elements, not absent utterances; word length is a cost table.
- **(iii) Computational opacity.** (a) `exp`/`log` eliminated by the ℕ-exponent + weight encoding; the equivalence is a comment-level encoding lemma. (b) `Qdiv` is total (`x/0 = 0`): undefined distributions are the zero function; every "whenever defined" theorem is an *iff* with a decidable condition and a companion `_undefined` theorem. (c) Irrational weights `e^{−λc}` are replaced by rational surrogates (Fig5: `1#50` for e^{−4}; Horn: `1#50`, `1#6250000` for e^{−4}, e^{−16}); theorems are about the surrogates, table in each example header. (d) `Qred` inside `normalize` is theory-invisible (`normalize_spec`) but computation-essential. (e) `Qeq` is a setoid: everything is `==`; `qsum`/`normalize`/`qpow` get explicit extensionality/`Proper` lemmas. (f) `vm_compute` yields unreduced fractions; concrete claims are `vm_compute; reflexivity` on `==`/`<` goals, never `reflexivity` alone. (g) α = 0 is total but degenerate (T9); `(0 < alpha)%nat` is threaded, not baked in.
- **(iv) Missing native structure.** No finite types, finite sets, big operators, probability monad or real analysis in the stdlib: finite sets are lists with `In`, Σ is `qsum` with its own algebra, cardinality is `length (filter …)`, `IsDist` is list-indexed, list order is spurious structure discharged by T25; continuous priors/integrals (L&G (30)–(32)) become finite grids and sums. Documented at `QSum` and `Threshold`.
- **(v) Decidability gap.** Sources are classical and real-valued; here meanings are `bool`, `consistent`/`expressible` are `existsb`, threshold comparisons are `Nat.ltb` on grid indices, rational order is decided by `Qlt_le_dec`. `subset_meaning` is a `Prop` but decidable via `forallb` (both forms provided). Two places where the formalization is *stronger* than the source are flagged: `NoDup ws` for cardinality (T6, T20) and the coverage hypothesis in T26–T27 (Bergen restriction (ii), which the L1 theorem needs only at one witness).

---

## 6. Pitfalls (all encountered or checked in the probe)

1. **`Qeq` is not `eq`.** Never `rewrite` with Leibniz equalities on `Q`; `f_equal`/`congruence` are useless; rewriting under `map`/`qsum` needs `qsum_map_ext_in` (no `Proper` for `map`). `Qplus`, `Qmult`, `Qdiv`, `Qinv`, `Qlt`, `Qle` already have morphisms.
2. **`vm_compute; reflexivity` closes `==` and `<` goals on closed rationals** (both unfold to `Z` comparisons of cross-products) — verified; `Qlt_alt`/`Qeq_alt` first also works. Never `simpl`/`cbn` on rationals.
3. **Numeric blowup.** Without `Qred` a 7-world α = 4 example does not finish; with `Qred` in `normalize` and around `qpow`, the whole probe (scalar, cookies, nine-lexica Horn) compiles in < 1 s. Never unfold `Qred` in proofs; go through `normalize_spec`/`Qred_correct`. Large numerators (Horn ≈ 10^67 unreduced-in-`show`) are harmless.
4. **Stdlib lemma names.** Present: `Qred_correct`, `Qmult_inv_r`, `Qmult_div_r`, `Qdiv_mult_l`, `Qmult_le_r/_l`, `Qmult_lt_r/_l`, `Qle_shift_div_l/_r`, `Qlt_shift_div_l/_r`, `Qinv_lt_0_compat`, `Qinv_le_0_compat`, `Qinv_lt_contravar`, `Qmult_le_0_compat`, `Qmult_lt_0_compat`, `Qmult_le_compat_nonneg`, `Qplus_le_compat`, `Qplus_lt_le_compat`, `Qle_lteq`, `Qlt_alt`, `Qeq_alt`, `Qle_bool_iff`, `Qeq_bool_iff`. Absent: `Qmult_inv_l`, `Qmult_le_compat_l`, `Qdiv_le_compat`, `Qlt_bool`, `Qpower_le_compat`. Division monotonicity is assembled from `Qmult_le_r` + `Qinv_lt_0_compat` or the `_shift_` lemmas.
5. **`field` on `Q`** works (`QArith` loads `Qfield`); side goals arrive as conjunctions of `~ x == 0`; discharge with `split; apply ne_of_lt; lra` (probe-verified). `ring` handles `Qdiv` after `unfold Qdiv`. `lra` (from `Lqa`) for linear goals; `nra` only for products of two variables — factor by hand deeper.
6. **α = 0 is degenerate** (`qpow _ 0 = 1`): `speaker_truthful`, `S1_undefined`, `L1_undefined`, support lemmas all need `(0 < alpha)%nat`; forgetting it is the most likely silent failure. Keep `alpha : nat`, do not use `S alpha'`.
7. **`Qpower` takes a `Z` exponent** and has no base-monotonicity lemmas; use the private `qpow`. The `^` notation in `Q_scope` is `Qpower` — don't use it.
8. **Scopes.** Under `Open Scope Q_scope`, `0`, `1`, `<`, `*` are rational; annotate `(0 < alpha)%nat`, `Z.of_nat`, `Nat.ltb`; prefer `1 # 3` over `1/3` in examples; `lra` needs no `nat` casts in the goal — convert `length` via `inject_Z (Z.of_nat …)` only in the statements that need it (T6, T20).
9. **Section discharge.** Section definitions become explicit-argument functions (`L1 W U ws us meaning prior costw alpha u w`); `vm_compute` sees through them (verified), but example modules must fix them with `Definition L1e := L1 _ _ ws us meaning prior costw 1` for readable statements. Hypotheses are added only to the theorems that use them; the header lists, per theorem, which hypotheses it needs (this is what makes the "exact definedness conditions" claim honest). Everything on a computation path must be `Definition`/`Defined`, never `Qed`.
10. **Generic step lemmas.** Prove `S_of_dist`, `S_of_support`, `L_of_dist`, `L_of_support`, `S_of_ext`, `L_of_ext` for an *arbitrary* input `L`/`S` satisfying the support invariant; otherwise the depth-n inductions (T23, T25, T26) cannot use their hypotheses. Then T7/T10 are instances at `L0`/`S1`.
11. **Lists as finite sets.** Duplicates double-count; `NoDup` only for cardinality; `In`-hypotheses threaded through every `filter`/`map` lemma (`in_map_iff`, `filter_In`, `existsb_exists`, `forallb_forall`).
12. **Nested sums (lexical uncertainty).** Positivity of `Σ_w prior w * Σ_L PL L * S1_lex L w u` needs a witness two levels deep; apply `qsum_pos_of_mem` twice rather than proving positivity ad hoc.
13. **Threshold grid.** Index heights and thresholds by `nat` and compare with `Nat.ltb`; map to `Q` only for priors/`PT`; avoid `Qeq_bool` chains on `Q` degrees.
14. **Index conventions.** Bergen's S_n reasons about L_{n−1}; G&F/L&G write S1/L1 for Bergen's n = 1; the file fixes `Sn (S m) := S_of (Ln m)` and states G&F's L1 = `Ln 1` explicitly, so T41's closed form `1/(2n+2)` with `p_0 = 1/2 = L0` has no off-by-one.

---

## 7. Build order (each step compiles on its own before the next starts)

1. Header comment (encoding lemma, sign note, artifact table skeleton), `Require`s, `Module QSum` with `qsum`, `qpow`, `normalize`, `normalize_spec`, `ne_of_lt`, T1–T2 algebra. Compile.
2. `Module Dist`: `IsDist`, `Pset`, `Pset_true`, `Pset_additive`, `normalize_nonneg/_sum/_zero/_ext_in`. Compile.
3. `Section RSA` definitions 6–15 and the decidability lemmas `consistent_iff`, `expressible_iff`. Compile; immediately add `Module ScalarImplicature` with T28–T30 by `vm_compute` as a smoke test of the definitions (cheap, catches argument-order mistakes early).
4. Generic step lemmas (`S_of_*`, `L_of_*`, pitfall 10), then T3–T6 (L0), T7–T9 (S1), T10–T12 (L1). Compile.
5. Bayes forms T13–T16; ordering T17–T19, T21; T31 (α-independent implicature, needs T19). Compile.
6. Invariance T22–T25; depth-n T26–T27; size principle T6/T20 last among MUST (fiddliest bookkeeping). Compile — all MUST items complete here.
7. MUST-lite example modules `Faces`, `BergenTwoWorlds`, `Cookies` (T32–T34) with fidelity notes. Compile.
8. STRETCH in order of value/cost: `Symmetry` (T35), `LexicalUncertainty` + `Fig5` + `Horn` (T36–T39, optionally T40), `BergenClosedForm` (T41), `Threshold` + `TallGrid` (T42–T45).
9. Final pass: fill the header's per-theorem hypothesis table and artifact table from the actual proofs; check `coqc` with the repo flags from the repo root; no `Admitted`, no axioms (`Print Assumptions` on the headline theorems).
