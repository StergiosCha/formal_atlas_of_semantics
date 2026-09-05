(* ========================================================================== *)
(*  DPL.v — Dynamic Predicate Logic                                           *)
(*  FORMAL-ATLAS / atlas/dynamic                                              *)
(* ========================================================================== *)
(*
   SOURCES
     Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic.
       Linguistics and Philosophy 14(1): 39–100.  Page references are given
       as "T n" (typescript/preprint, the text-searchable copy in
       papers/dynamic/Groenendijk_Stokhof_1991_DPL_preprint.pdf) and "P n"
       (journal pagination), following the design document.
       [§2 (the system, donkey sentences: T 2–13 / P 40–53); §3.1–3.2
        (Def. 1–12, Facts 1–6: T 13–17 / P 53–58); §3.3 (Def. 13–16,
        Facts 7–9: T 18–19 / P 58–61); §3.4 (the displayed laws D1–D50:
        T 20–25 / P 61–66; Def. 17 closure: T 22 / P 63); §3.5 (Def. 18–22,
        Facts 10–16: T 25–29 / P 66–70)]
     Dekker, P. (2012). Dynamic Semantics. Springer.  [§2.1 Def. 1,
       Observations 1–2 = D46/D48 below (Egli's Theorem and Corollary)]
   Design document: formalizing_formal_semantics/atlas/designs/dpl.md
     (D1..D50 numbers the unnumbered displayed laws of §3.4 in reading
      order; "Fact n" is the source's own numbering).

   WHAT IS FORMALIZED
     Part 1  Preliminaries: variables (Var := nat), assignments, update
             g[x := d], the source's "k differs from g at most in x" (k[x]g),
             agreement on a variable set (g =_V h), list-set helpers.
     Part 2  Syntax (Def. 1): terms over a signature, formulas with atoms,
             identity, and ALL EIGHT connectives ¬ ∧ ∨ → ∃ ∀ primitive, so
             the interdefinability laws D1–D3 are theorems, not definitions;
             the closure operator ♦ as the formula-level surrogate ¬¬
             (licensed by D19).
     Part 3  Models ⟨D,F⟩ with D inhabited, total assignments, term values.
     Part 4  Semantics (Def. 2) as a relation between assignments, factored
             through eight relation operators (rtest, rcomp, rneg, rdisj,
             rimpl, rex, rall, rclos); [sem] unfolds to Def. 2's set-builder
             clauses literally (orientation "h = g" kept everywhere).
     Part 5  Semantic notions: truth (Def. 3), validity/contradiction
             (Def. 4–5), satisfaction and production sets (Def. 6, 9),
             s-equivalence, equivalence, p-equivalence (Def. 7, 8, 10),
             tests (Def. 11), conditions (Def. 12, with ∀ restored — see
             SOURCE NOTES), the entailment notions (Def. 18–22): s-entailment,
             meaning inclusion, dynamic entailment, x̄-entailment, and
             entailment from a sequence of premisses.
     Part 6  Facts 1–6 of §3.2 (Fact 6's converse REFUTED: fact6_refuted),
             the static/dynamic distinction (every ¬/∨/→/∀/♦/atom/= formula
             is a test; ∃xPx is not: not_test_ex).
     Part 7  Binding at the variable level (Def. 15–16): AQV, FV; Fact 9,
             its corollaries, the transfer lemma (the induction underlying
             the source's proofs of Facts 8, 13–16 and the conditional laws
             of §3.4), Fact 8.
     Part 8  §3.4: the unconditional laws D1–D3, D7, D9, D10, D16, D17,
             D19–D27, D30, D31, D34–D38, D40, D41, D43–D46, D48 (D46 = Egli's
             Theorem, D48 = Egli's Corollary, D27 = associativity of ∧),
             the conditional laws D14, D32, D33, D39, D42, D47 with their
             AQV/FV side conditions, and the iff-test laws D18 and D20.
     Part 9  Countermodels over a two-element domain: the non-equivalences
             D4, D5, D6, D8, D11, D12, D28, D29, D49, Fact 3, the headline
             ¬¬∃xPx ≄ ∃xPx (negneg_witness, negneg_not_equiv), and the
             refutation of the printed idempotency-of-∨ law (SOURCE NOTES).
     Part 10 §3.5: Facts 10–16 (deduction theorem, ♦-reduction, coincidence
             and transfer under AQV∩FV = ∅, restricted reflexivity and
             transitivity), the source's separating examples (∃xPx ⊨ Px but
             ∃xPx ⊭s Px, mutual entailment without equivalence,
             non-reflexivity, non-transitivity), order-sensitivity of
             sequence entailment.
     Part 11 The donkey sentences (§2.3–2.5): dk1 "A farmer owns a donkey.
             He beats it." (shape (1b)), dk2 "If a farmer owns a donkey, he
             beats it." ((2b)), dk3 "Every farmer who owns a donkey beats
             it" ((3b)); their relational meanings and first-order truth
             conditions proved as biconditionals over an arbitrary domain,
             and equiv dk2 dk3 via Egli's Corollary.
     Part 12 Assumption audit (Print Assumptions for every main theorem).

   NOT FORMALIZED (and why)
     * Occurrence-level binding (Def. 13–14: bp, aq, fv, sp) and Fact 7
       (sp(φ) ⊆ bp(φ)): the source itself calls Def. 13 "a bit sloppy" for
       want of an occurrence notation; every later Fact and law uses only
       the variable-level shadows FV/AQV (Def. 15–16), which are formalized.
     * D50 (∃xφ ≃s ∃y[y/x]φ if y ∉ FV(φ)): needs a DPL-aware substitution
       operator, and the printed side condition is insufficient (it admits
       capture, e.g. φ := ∃y Rxy needs "y does not occur in φ"); left out
       with the design's STRETCH-5 clause, together with the substitution
       operator itself.  The non-equivalence half D49 IS proved.
     * D13 and D15 (the prose iff-laws "φ∧ψ ≃ ¬(φ→¬ψ) iff φ∧ψ is a test"
       and "∃xφ ≃ ¬∀x¬φ iff ∃xφ is a test") and the refutation of the P 62
       rider on D15: design STRETCH items, dropped for budget.  The
       corresponding ♦-equivalences (D23–D26) and the iff-laws D18
       (¬¬φ ≃ φ iff φ is a test) and D20 (♦φ ≃ ♦ψ ⇔ φ ≃s ψ) ARE proved.
     * §3.6/§4 (PL normal binding form, Facts 17–29, DRT, QDL) and §5:
       sibling atlas files per the design's scope.
     * The sequence-entailment ⇔ big-conjunction display of P 70 and the
       §2.3–2.5 worked-example meaning computations: design STRETCH 1–2,
       dropped for budget; order-sensitivity and non-monotonicity of
       sequence entailment ARE proved (seq_entailment_order_sensitive,
       entails_seq_nonmonotonic).

   SOURCE NOTES (discrepancies recorded here and at the theorems)
     * Def. 12 (conditions) omits universally quantified formulas in both
       editions, while the sentence preceding it lists them among the tests
       and Fact 5 requires them; ∀xφ is restored as a condition here
       (constructor cond_all).
     * Fact 6 claims "φ is a test iff φ is a condition or a contradiction".
       With identity in the language the left-to-right direction is FALSE:
       x = y ∧ ∃x[x = y] is a test but neither a condition nor a
       contradiction (theorem fact6_refuted).  The right-to-left direction
       is proved (fact6_if).
     * §3.4 prints "φ ≃ φ ∨ φ" as an unconditional law ("disjunction ...
       is unconditionally idempotent", T 23 / P 64, D34).  By Def. 2
       clause 5, φ ∨ φ is a TEST (it equals ♦φ), so the law fails for
       φ := ∃xPx: theorem d34_refuted.  What does hold, and is proved
       here: ♦φ ≃ φ ∨ φ (d34_clos), φ ≃s φ ∨ φ (d34_s_equiv), and
       φ ≃ φ ∨ φ for tests (d34_test).
     * The typescript prints the idempotency non-law as φ ≄ ψ ∧ φ (typo);
       the journal (P 63) has φ ≄ φ ∧ φ; the prose ("counterexample against
       idempotency ... Qx ∧ ∃xPx") settles it (theorem d29).
     * The printed proof of Fact 16 (T 29 / P 69) swaps AQV(ψ) ∩ FV(χ) to
       "AQV(χ) ∩ FV(ψ)" in one line; the Fact's statement is the correct
       one and is what is proved (fact16).

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-i]   [sem] must be a Fixpoint into Prop, not an Inductive
                    relation: the ¬, →, ∀ clauses contain "¬∃" and
                    "∀ ... → ∃", non-positive occurrences.
     [ARTIFACT-ii]  model Σ packs D : Type, so equiv/valid/test/entails
                    quantify over a large type inside Prop (impredicativity,
                    harmless); the source's sets ([[φ]] ⊆ G×G, \φ\, /φ/)
                    are Prop-valued functions, compared by pointwise iff
                    (rel_eq), never by Leibniz equality.
     [ARTIFACT-iii] sem/true_wrt/test/equiv/entails never compute;
                    countermodels are proved, not evaluated; only upd, tval,
                    AQV, FV compute (Eval-compute sanity checks in Part 11).
     [ARTIFACT-iv]  (a) The source's assignments are set-theoretic functions,
                    hence extensional: FunctionalExtensionality is imported,
                    used ONLY where a Leibniz-equal output assignment is
                    required (fact6_refuted, transfer_given, D32/D33/D47,
                    dk1_meaning) and tracked in Part 12; the headline
                    theorems (Egli, associativity, negneg_witness, Fact 9,
                    dk1_truth, dk2_truth) are axiom-free.  (b) Occurrences
                    have no representation (see NOT FORMALIZED).  (c) Fixed
                    arity is not enforced: F(R) takes a list (wf_arity is
                    defined but no theorem hypothesizes it).  (d) ♦ is not
                    syntax: rclos at relation level, Clos φ := ¬¬φ at
                    formula level, licensed by D19.  (e) Premiss sequences
                    (Def. 22) are lists with a chained composition.
     [ARTIFACT-v]   Var := nat supplies the decidable equality of variables
                    the source uses silently (update, FV/AQV membership);
                    Classical is imported globally — the source's metatheory
                    is classical (used for D1, D2, D7, D9, D10, D17, D18,
                    D21–D26, D38, D40–D42, D14, Facts 3, 12; everything
                    else is constructive, see Part 12).
*)

Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Classical.
Require Import FunctionalExtensionality.

(* ========================================================================== *)
(*  Part 1 — Preliminaries: variables, assignments, agreement                 *)
(* ========================================================================== *)

(* Def. 1 preamble (T 13 / P 53): "an infinite set of variables"; nat gives
   the decidable identity of symbols the source uses silently [ARTIFACT-v]. *)
Definition Var : Type := nat.

(* Assignments over a domain D: "an assignment g is a function assigning an
   individual to each variable" (T 14 / P 54); total, as in the source. *)
Definition Assign (D : Type) : Type := Var -> D.

(* g[x := d], the update needed to build witnesses for the ∃/∀ clauses. *)
Definition upd {D : Type} (g : Assign D) (x : Var) (d : D) : Assign D :=
  fun y => if Nat.eq_dec y x then d else g y.

Lemma upd_eq : forall D (g : Assign D) x d, upd g x d x = d.
Proof. intros; unfold upd; destruct (Nat.eq_dec x x); congruence. Qed.

Lemma upd_neq : forall D (g : Assign D) x d y, y <> x -> upd g x d y = g y.
Proof. intros; unfold upd; destruct (Nat.eq_dec y x); congruence. Qed.

(* k[x]g — "h differs at most with respect to x from g" (§2.3 T 6 / P 45),
   stated pointwise so that witnesses are cheap. *)
Definition dif {D : Type} (x : Var) (k g : Assign D) : Prop :=
  forall y, y <> x -> k y = g y.

Lemma dif_refl : forall D x (g : Assign D), dif x g g.
Proof. intros D x g y Hy; reflexivity. Qed.

Lemma dif_upd : forall D (g : Assign D) x d, dif x (upd g x d) g.
Proof. intros D g x d y Hy; apply upd_neq; assumption. Qed.

Lemma dif_sym : forall D x (k g : Assign D), dif x k g -> dif x g k.
Proof. intros D x k g H y Hy; symmetry; apply H; assumption. Qed.

Lemma dif_trans : forall D x (k m g : Assign D), dif x k m -> dif x m g -> dif x k g.
Proof. intros D x k m g H1 H2 y Hy; rewrite (H1 y Hy); apply H2; assumption. Qed.

(* Extensionality of assignments: the source's g = h (Def. 2, Def. 11) is
   equality of set-theoretic functions [ARTIFACT-iv(a)]. *)
Lemma assign_ext : forall D (g h : Assign D), (forall v, g v = h v) -> g = h.
Proof. intros D g h H; apply functional_extensionality; assumption. Qed.

(* g =_V h — "for all x ∈ V: g(x) = h(x)" (preamble to Fact 8, T 19 / P 61,
   and Def. 21, T 28 / P 69). *)
Definition agree {D : Type} (V : list Var) (g h : Assign D) : Prop :=
  forall v, In v V -> g v = h v.

Lemma agree_refl : forall D V (g : Assign D), agree V g g.
Proof. intros D V g v Hv; reflexivity. Qed.

Lemma agree_sym : forall D V (g h : Assign D), agree V g h -> agree V h g.
Proof. intros D V g h H v Hv; symmetry; apply H; assumption. Qed.

Lemma agree_trans : forall D V (g k h : Assign D),
  agree V g k -> agree V k h -> agree V g h.
Proof. intros D V g k h H1 H2 v Hv; rewrite (H1 v Hv); apply H2; assumption. Qed.

Lemma agree_app_l : forall D V W (g h : Assign D), agree (V ++ W) g h -> agree V g h.
Proof. intros D V W g h H v Hv; apply H, in_or_app; auto. Qed.

Lemma agree_app_r : forall D V W (g h : Assign D), agree (V ++ W) g h -> agree W g h.
Proof. intros D V W g h H v Hv; apply H, in_or_app; auto. Qed.

Lemma agree_incl : forall D V W (g h : Assign D),
  (forall v, In v V -> In v W) -> agree W g h -> agree V g h.
Proof. intros D V W g h Hincl H v Hv; apply H, Hincl; assumption. Qed.

(* AQV(φ) ∩ FV(ψ) = ∅, the side condition of Facts 13–16 and D14/D32/D33/
   D39/D42 (T 26–29 / P 62–68), as a Prop over membership. *)
Definition disjoint (V W : list Var) : Prop :=
  forall v, In v V -> ~ In v W.

(* List intersection, for the AQV(ψ) ∩ FV(χ) subscript of Fact 16. *)
Definition inter (V W : list Var) : list Var :=
  filter (fun v => if in_dec Nat.eq_dec v W then true else false) V.

Lemma inter_In : forall V W v, In v (inter V W) <-> In v V /\ In v W.
Proof.
  intros V W v; unfold inter; rewrite filter_In.
  destruct (in_dec Nat.eq_dec v W); intuition congruence.
Qed.

(* ========================================================================== *)
(*  Part 2 — Syntax (Def. 1, T 13 / P 53)                                     *)
(* ========================================================================== *)

(* The non-logical vocabulary: "n-place predicates" and "individual
   constants" (Def. 1 preamble).  One object to quantify over. *)
Record signature : Type := {
  Pred  : Type;
  arity : Pred -> nat;
  Const : Type
}.

(* Terms: "individual constants and variables" (Def. 1). *)
Inductive term (Σ : signature) : Type :=
| TVar : Var -> term Σ
| TCon : Const Σ -> term Σ.
Arguments TVar {Σ} _.
Arguments TCon {Σ} _.

(* Def. 1: atoms Rt1...tn, identity t1 = t2, and all eight connectives as
   primitive constructors, so the interdefinability displays D1–D3 are
   theorems (T 20 / P 61), not definitions. *)
Inductive form (Σ : signature) : Type :=
| Atom : Pred Σ -> list (term Σ) -> form Σ
| Eq   : term Σ -> term Σ -> form Σ
| Neg  : form Σ -> form Σ
| Conj : form Σ -> form Σ -> form Σ
| Disj : form Σ -> form Σ -> form Σ
| Impl : form Σ -> form Σ -> form Σ
| Ex   : Var -> form Σ -> form Σ
| All  : Var -> form Σ -> form Σ.
Arguments Atom {Σ} _ _.
Arguments Eq   {Σ} _ _.
Arguments Neg  {Σ} _.
Arguments Conj {Σ} _ _.
Arguments Disj {Σ} _ _.
Arguments Impl {Σ} _ _.
Arguments Ex   {Σ} _ _.
Arguments All  {Σ} _ _.

(* ♦ (Def. 17, T 22 / P 63) is not part of Def. 1's syntax; the source's own
   law D19 "♦φ ≃ ¬¬φ" licenses the surrogate [ARTIFACT-iv(d)]. *)
Definition Clos {Σ} (φ : form Σ) : form Σ := Neg (Neg φ).

(* "F(R) ⊆ D^n" is not enforced by typing [ARTIFACT-iv(c)]: wf_arity is
   definable but no theorem below hypothesizes it. *)
Fixpoint wf_arity {Σ} (φ : form Σ) : Prop :=
  match φ with
  | Atom R ts   => length ts = arity Σ R
  | Eq _ _      => True
  | Neg φ       => wf_arity φ
  | Conj φ ψ | Disj φ ψ | Impl φ ψ => wf_arity φ /\ wf_arity ψ
  | Ex _ φ | All _ φ => wf_arity φ
  end.

Declare Scope dpl_scope.
Delimit Scope dpl_scope with dpl.
Notation "t =' u"  := (Eq t u)    (at level 70)  : dpl_scope.
Notation "¬' φ"    := (Neg φ)     (at level 75)  : dpl_scope.
Notation "φ ∧' ψ"  := (Conj φ ψ)  (at level 80, right associativity) : dpl_scope.
Notation "φ ∨' ψ"  := (Disj φ ψ)  (at level 85, right associativity) : dpl_scope.
Notation "φ →' ψ"  := (Impl φ ψ)  (at level 90, right associativity) : dpl_scope.
Notation "∃' x , φ" := (Ex x φ)   (at level 95, x at level 0) : dpl_scope.
Notation "∀' x , φ" := (All x φ)  (at level 95, x at level 0) : dpl_scope.

(* ========================================================================== *)
(*  Part 3 — Models and assignments (T 13–14 / P 53–54)                        *)
(* ========================================================================== *)

(* "A model M is a pair ⟨D, F⟩, D a non-empty set of individuals, F an
   interpretation function": dom_inh records non-emptiness (used only by
   countermodels); F(R) ⊆ D^n is a predicate on lists [ARTIFACT-iv(c)]. *)
Record model (Σ : signature) : Type := Build_model {
  dom     : Type;
  dom_inh : dom;
  F_con   : Const Σ -> dom;
  F_pred  : Pred Σ -> list dom -> Prop
}.
Arguments dom     {Σ} _.
Arguments dom_inh {Σ} _.
Arguments F_con   {Σ} _ _.
Arguments F_pred  {Σ} _ _ _.

(* G, "the set of all assignment functions" (T 14 / P 54). *)
Definition G {Σ} (M : model Σ) : Type := Assign (dom M).

(* ⟦t⟧_g = g(t) if t is a variable, F(t) if a constant (T 14 / P 54). *)
Definition tval {Σ} (M : model Σ) (g : G M) (t : term Σ) : dom M :=
  match t with
  | TVar v => g v
  | TCon c => F_con M c
  end.

(* ========================================================================== *)
(*  Part 4 — The relation layer and the semantics (Def. 2, T 14 / P 54)        *)
(* ========================================================================== *)

(* "⟦ ⟧ ⊆ G × G": relations between assignments, compared pointwise
   [ARTIFACT-ii] — never by Leibniz equality. *)
Definition Rel (A : Type) : Type := A -> A -> Prop.

Definition rel_eq {A} (R S : Rel A) : Prop := forall g h, R g h <-> S g h.
Definition rel_incl {A} (R S : Rel A) : Prop := forall g h, R g h -> S g h.

Lemma rel_eq_refl : forall A (R : Rel A), rel_eq R R.
Proof. intros A R g h; reflexivity. Qed.
Lemma rel_eq_sym : forall A (R S : Rel A), rel_eq R S -> rel_eq S R.
Proof. intros A R S H g h; symmetry; apply H. Qed.
Lemma rel_eq_trans : forall A (R S T : Rel A), rel_eq R S -> rel_eq S T -> rel_eq R T.
Proof. intros A R S T H1 H2 g h; rewrite (H1 g h); apply H2. Qed.

(* The satisfaction and production sets of a relation (Def. 6, 9 lifted to
   the relation layer), and the test property (Def. 11 remark). *)
Definition sat  {A} (R : Rel A) (g : A) : Prop := exists h, R g h.
Definition rprod {A} (R : Rel A) (h : A) : Prop := exists g, R g h.
Definition is_test_rel {A} (R : Rel A) : Prop := forall g h, R g h -> h = g.

(* The eight clause shapes of Def. 2 plus Def. 17.  Each rtest keeps the
   source's "h = g & ... h ..." orientation verbatim. *)
Definition rtest {A} (P : A -> Prop) : Rel A :=
  fun g h => h = g /\ P h.
Definition rcomp {A} (R S : Rel A) : Rel A :=
  fun g h => exists k, R g k /\ S k h.
Definition rneg {A} (R : Rel A) : Rel A :=
  rtest (fun h => ~ exists k, R h k).
Definition rdisj {A} (R S : Rel A) : Rel A :=
  rtest (fun h => exists k, R h k \/ S h k).
Definition rimpl {A} (R S : Rel A) : Rel A :=
  rtest (fun h => forall k, R h k -> exists j, S k j).
Definition rex {D} (x : Var) (R : Rel (Assign D)) : Rel (Assign D) :=
  fun g h => exists k, dif x k g /\ R k h.
Definition rall {D} (x : Var) (R : Rel (Assign D)) : Rel (Assign D) :=
  rtest (fun h => forall k, dif x k h -> exists j, R k j).
(* Def. 17 (Closure): ⟦♦φ⟧ = {⟨g,h⟩ | g = h & ∃k: ⟨h,k⟩ ∈ ⟦φ⟧} (T 22 / P 63). *)
Definition rclos {A} (R : Rel A) : Rel A :=
  rtest (fun h => exists k, R h k).

(* Def. 2 clauses 1–2: atoms and identity are tests on the current
   assignment. *)
Definition ratom {Σ} (M : model Σ) (R : Pred Σ) (ts : list (term Σ)) : Rel (G M) :=
  rtest (fun h => F_pred M R (map (tval M h) ts)).
Definition req {Σ} (M : model Σ) (t1 t2 : term Σ) : Rel (G M) :=
  rtest (fun h => tval M h t1 = tval M h t2).

(* Def. 2 (Semantics), all eight clauses.  [ARTIFACT-i]: a Fixpoint into
   Prop — an Inductive relation is impossible because the ¬, →, ∀ clauses
   contain non-positive occurrences (¬∃, ∀...→∃). *)
Fixpoint sem {Σ} (M : model Σ) (φ : form Σ) : Rel (G M) :=
  match φ with
  | Atom R ts => ratom M R ts
  | Eq t1 t2  => req M t1 t2
  | Neg φ     => rneg  (sem M φ)
  | Conj φ ψ  => rcomp (sem M φ) (sem M ψ)
  | Disj φ ψ  => rdisj (sem M φ) (sem M ψ)
  | Impl φ ψ  => rimpl (sem M φ) (sem M ψ)
  | Ex x φ    => rex  x (sem M φ)
  | All x φ   => rall x (sem M φ)
  end.

(* R1: the eight unfolding lemmas — [sem] yields Def. 2's clauses literally. *)
Lemma sem_atom : forall Σ (M : model Σ) R ts, sem M (Atom R ts) = ratom M R ts.
Proof. reflexivity. Qed.
Lemma sem_eq : forall Σ (M : model Σ) t1 t2, sem M (Eq t1 t2) = req M t1 t2.
Proof. reflexivity. Qed.
Lemma sem_neg : forall Σ (M : model Σ) φ, sem M (Neg φ) = rneg (sem M φ).
Proof. reflexivity. Qed.
Lemma sem_conj : forall Σ (M : model Σ) φ ψ, sem M (Conj φ ψ) = rcomp (sem M φ) (sem M ψ).
Proof. reflexivity. Qed.
Lemma sem_disj : forall Σ (M : model Σ) φ ψ, sem M (Disj φ ψ) = rdisj (sem M φ) (sem M ψ).
Proof. reflexivity. Qed.
Lemma sem_impl : forall Σ (M : model Σ) φ ψ, sem M (Impl φ ψ) = rimpl (sem M φ) (sem M ψ).
Proof. reflexivity. Qed.
Lemma sem_ex : forall Σ (M : model Σ) x φ, sem M (Ex x φ) = rex x (sem M φ).
Proof. reflexivity. Qed.
Lemma sem_all : forall Σ (M : model Σ) x φ, sem M (All x φ) = rall x (sem M φ).
Proof. reflexivity. Qed.

(* The formula-level ♦ surrogate has the meaning Def. 17 prescribes
   (classical: ¬¬∃ collapses to ∃). *)
Lemma sem_clos : forall Σ (M : model Σ) (φ : form Σ),
  rel_eq (sem M (Clos φ)) (rclos (sem M φ)).
Proof.
  intros Σ M φ g h; simpl; unfold rneg, rclos, rtest; split.
  - intros [-> Hn]; split; [reflexivity |].
    apply NNPP; intro Hno; apply Hn; exists g; split; [reflexivity | exact Hno].
  - intros [-> Hs]; split; [reflexivity |].
    intros [k [-> Hn]]; exact (Hn Hs).
Qed.

(* ========================================================================== *)
(*  Part 5 — Semantic notions (Def. 3–12, T 15–17 / P 55–58)                   *)
(*  and the entailment notions (Def. 18–22, T 25–29 / P 66–70)                 *)
(* ========================================================================== *)

(* Def. 3 (Truth): "φ is true with respect to g in M iff ∃h: ⟨g,h⟩ ∈ ⟦φ⟧". *)
Definition true_wrt {Σ} (M : model Σ) (φ : form Σ) (g : G M) : Prop :=
  exists h, sem M φ g h.

(* Def. 4 (Validity) and Def. 5 (Contradictoriness). *)
Definition valid {Σ} (φ : form Σ) : Prop :=
  forall (M : model Σ) (g : G M), true_wrt M φ g.
Definition contradiction {Σ} (φ : form Σ) : Prop :=
  forall (M : model Σ) (g : G M), ~ true_wrt M φ g.

(* Def. 6 (Satisfaction set) \φ\_M and Def. 9 (Production set) /φ/_M. *)
Definition sat_set {Σ} (M : model Σ) (φ : form Σ) : G M -> Prop :=
  fun g => exists h, sem M φ g h.
Definition prod_set {Σ} (M : model Σ) (φ : form Σ) : G M -> Prop :=
  fun h => exists g, sem M φ g h.

(* Def. 7, 8, 10: s-equivalence, equivalence simpliciter, p-equivalence.
   Set identity is pointwise iff [ARTIFACT-ii]. *)
Definition s_equiv {Σ} (φ ψ : form Σ) : Prop :=
  forall M (g : G M), sat_set M φ g <-> sat_set M ψ g.
Definition equiv {Σ} (φ ψ : form Σ) : Prop :=
  forall M, rel_eq (sem M φ) (sem M ψ).
Definition p_equiv {Σ} (φ ψ : form Σ) : Prop :=
  forall M (h : G M), prod_set M φ h <-> prod_set M ψ h.

Lemma equiv_refl : forall Σ (φ : form Σ), equiv φ φ.
Proof. intros Σ φ M; apply rel_eq_refl. Qed.
Lemma equiv_sym : forall Σ (φ ψ : form Σ), equiv φ ψ -> equiv ψ φ.
Proof. intros Σ φ ψ H M; apply rel_eq_sym, H. Qed.
Lemma equiv_trans : forall Σ (φ ψ χ : form Σ), equiv φ ψ -> equiv ψ χ -> equiv φ χ.
Proof. intros Σ φ ψ χ H1 H2 M; eapply rel_eq_trans; [apply H1 | apply H2]. Qed.

(* Def. 11 (Test): "φ is a test iff ∀M: ⟦φ⟧ ⊆ {⟨g,g⟩}" — with the source's
   set-theoretic identity of assignments read as Leibniz equality
   [ARTIFACT-iv(a)]; the h = g orientation matches Def. 2. *)
Definition test {Σ} (φ : form Σ) : Prop :=
  forall M (g h : G M), sem M φ g h -> h = g.

(* Def. 12 (Conditions).  SOURCE NOTE: as printed (T 17 / P 57) the list
   omits universally quantified formulas in both editions, although the
   preceding sentence counts them among the tests and Fact 5 needs them;
   cond_all restores the ∀ clause. *)
Inductive condition {Σ} : form Σ -> Prop :=
| cond_atom : forall R ts, condition (Atom R ts)
| cond_eq   : forall t1 t2, condition (Eq t1 t2)
| cond_neg  : forall φ, condition (Neg φ)
| cond_disj : forall φ ψ, condition (Disj φ ψ)
| cond_impl : forall φ ψ, condition (Impl φ ψ)
| cond_all  : forall x φ, condition (All x φ)
| cond_conj : forall φ ψ, condition φ -> condition ψ -> condition (Conj φ ψ).

(* Def. 18 (s-entailment): truth preservation, ∀M: \φ\ ⊆ \ψ\. *)
Definition s_entails {Σ} (φ ψ : form Σ) : Prop :=
  forall M (g : G M), true_wrt M φ g -> true_wrt M ψ g.

(* Def. 19 (Meaning inclusion): ∀M: ⟦φ⟧ ⊆ ⟦ψ⟧. *)
Definition meaning_incl {Σ} (φ ψ : form Σ) : Prop :=
  forall M, rel_incl (sem M φ) (sem M ψ).

(* Def. 20 (Dynamic entailment): "every assignment that is a possible output
   of φ is a possible input for ψ". *)
Definition entails {Σ} (φ ψ : form Σ) : Prop :=
  forall M (g h : G M), sem M φ g h -> true_wrt M ψ h.

(* The source's "more economically: φ ⊨ ψ iff ∀M: /φ/ ⊆ \ψ\" (T 26 / P 67). *)
Lemma entails_prod_sat : forall Σ (φ ψ : form Σ),
  entails φ ψ <-> forall M (h : G M), prod_set M φ h -> sat_set M ψ h.
Proof.
  intros Σ φ ψ; split.
  - intros H M h [g Hg]; exact (H M g h Hg).
  - intros H M g h Hg; apply (H M h); exists g; exact Hg.
Qed.

(* Def. 21 (x1...xn-Entailment): the conclusion has an output agreeing with
   the input on x1...xn (T 28 / P 69). *)
Definition entails_vars {Σ} (xs : list Var) (φ ψ : form Σ) : Prop :=
  forall M (g : G M), prod_set M φ g ->
    exists h, sem M ψ g h /\ agree xs h g.

(* Def. 22 (Entailment, general form): the premisses are "a sequence, not a
   set" (T 29 / P 70) — a list, composed left to right. *)
Fixpoint sem_seq {Σ} (M : model Σ) (Γ : list (form Σ)) : Rel (G M) :=
  match Γ with
  | []      => fun g h => h = g
  | φ :: Γ' => rcomp (sem M φ) (sem_seq M Γ')
  end.

Definition entails_seq {Σ} (Γ : list (form Σ)) (ψ : form Σ) : Prop :=
  forall M (g h : G M), sem_seq M Γ g h -> true_wrt M ψ h.

(* ========================================================================== *)
(*  Part 6 — Tests, the static/dynamic distinction, Facts 1–6 (§3.2)          *)
(* ========================================================================== *)

(* Def. 11 remark (T 17 / P 57): every rtest-shaped clause is a test. *)
Lemma rtest_is_test : forall A (P : A -> Prop), is_test_rel (rtest P).
Proof. intros A P g h [E _]; exact E. Qed.

Lemma sat_rtest : forall A (P : A -> Prop) (g : A), sat (rtest P) g <-> P g.
Proof.
  intros A P g; split.
  - intros [h [-> Hh]]; exact Hh.
  - intros Hg; exists g; split; [reflexivity | exact Hg].
Qed.

(* R2: atoms, identity, ¬, ∨, →, ∀ and ♦ are tests — the "externally static"
   connectives (§2.4 T 10 / P 49 for →, §2.5 T 11 / P 50 for ∀, Def. 12
   remark for the rest); ∧ preserves testhood. *)
Lemma test_atom : forall Σ (R : Pred Σ) ts, test (Atom R ts).
Proof. intros Σ R ts M g h [E _]; exact E. Qed.
Lemma test_eq : forall Σ (t1 t2 : term Σ), test (Eq t1 t2).
Proof. intros Σ t1 t2 M g h [E _]; exact E. Qed.
Lemma test_neg : forall Σ (φ : form Σ), test (Neg φ).
Proof. intros Σ φ M g h [E _]; exact E. Qed.
Lemma test_disj : forall Σ (φ ψ : form Σ), test (Disj φ ψ).
Proof. intros Σ φ ψ M g h [E _]; exact E. Qed.
Lemma test_impl : forall Σ (φ ψ : form Σ), test (Impl φ ψ).
Proof. intros Σ φ ψ M g h [E _]; exact E. Qed.
Lemma test_all : forall Σ x (φ : form Σ), test (All x φ).
Proof. intros Σ x φ M g h [E _]; exact E. Qed.
Lemma test_clos : forall Σ (φ : form Σ), test (Clos φ).
Proof. intros Σ φ; apply test_neg. Qed.
Lemma test_conj : forall Σ (φ ψ : form Σ), test φ -> test ψ -> test (Conj φ ψ).
Proof.
  intros Σ φ ψ Hφ Hψ M g h [k [H1 H2]].
  rewrite (Hψ M k h H2); exact (Hφ M g k H1).
Qed.

(* R3: for a test, truth "boils down to ⟨g,g⟩ ∈ ⟦φ⟧" (T 17 / P 57). *)
Lemma true_wrt_test : forall Σ (M : model Σ) (φ : form Σ) (g : G M),
  test φ -> (true_wrt M φ g <-> sem M φ g g).
Proof.
  intros Σ M φ g Ht; split.
  - intros [h Hh]; assert (E := Ht M g h Hh); subst h; exact Hh.
  - intros Hg; exists g; exact Hg.
Qed.

(* G&S 1991 §3.2, Fact 1 (T 16 / P 56): equivalence implies s-equivalence. *)
Theorem fact1 : forall Σ (φ ψ : form Σ), equiv φ ψ -> s_equiv φ ψ.
Proof.
  intros Σ φ ψ H M g; split; intros [h Hh]; exists h; apply H; exact Hh.
Qed.

(* G&S 1991 §3.2, Fact 2 (T 16 / P 56): equivalence implies p-equivalence. *)
Theorem fact2 : forall Σ (φ ψ : form Σ), equiv φ ψ -> p_equiv φ ψ.
Proof.
  intros Σ φ ψ H M h; split; intros [g Hg]; exists g; apply H; exact Hg.
Qed.

(* G&S 1991 §3.2, Fact 4 (T 17 / P 57): for tests, the three equivalence
   notions coincide. *)
Theorem fact4 : forall Σ (φ ψ : form Σ), test φ -> test ψ ->
  (s_equiv φ ψ <-> equiv φ ψ) /\ (equiv φ ψ <-> p_equiv φ ψ).
Proof.
  intros Σ φ ψ Hφ Hψ; split; split.
  - (* s_equiv -> equiv *)
    intros Hs M g h; split; intro Hgh.
    + assert (E := Hφ M g h Hgh); subst h.
      destruct (proj1 (Hs M g)) as [h' Hh']; [exists g; exact Hgh |].
      assert (E' := Hψ M g h' Hh'); subst h'; exact Hh'.
    + assert (E := Hψ M g h Hgh); subst h.
      destruct (proj2 (Hs M g)) as [h' Hh']; [exists g; exact Hgh |].
      assert (E' := Hφ M g h' Hh'); subst h'; exact Hh'.
  - apply fact1.
  - apply fact2.
  - (* p_equiv -> equiv *)
    intros Hp M g h; split; intro Hgh.
    + assert (E := Hφ M g h Hgh); subst h.
      destruct (proj1 (Hp M g)) as [g' Hg']; [exists g; exact Hgh |].
      assert (E' := Hψ M g' g Hg'); subst g'; exact Hg'.
    + assert (E := Hψ M g h Hgh); subst h.
      destruct (proj2 (Hp M g)) as [g' Hg']; [exists g; exact Hgh |].
      assert (E' := Hφ M g' g Hg'); subst g'; exact Hg'.
Qed.

(* G&S 1991 §3.2, Fact 5 (T 17 / P 58): every condition is a test. *)
Theorem fact5 : forall Σ (φ : form Σ), condition φ -> test φ.
Proof.
  intros Σ φ Hc; induction Hc.
  - apply test_atom.
  - apply test_eq.
  - apply test_neg.
  - apply test_disj.
  - apply test_impl.
  - apply test_all.
  - apply test_conj; assumption.
Qed.

(* G&S 1991 §3.2, Fact 6, ⇐ direction (T 17 / P 58): conditions and
   contradictions are tests.  The ⇒ direction is REFUTED below
   (fact6_refuted). *)
Theorem fact6_if : forall Σ (φ : form Σ),
  condition φ \/ contradiction φ -> test φ.
Proof.
  intros Σ φ [Hc | Hc].
  - apply fact5; exact Hc.
  - intros M g h Hgh; exfalso; apply (Hc M g); exists h; exact Hgh.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The concrete signature for countermodels: one-place P, Q, two-place R.    *)
(* -------------------------------------------------------------------------- *)

Inductive pred_ex : Type := Pe | Qe | Re2.

Definition Σ_ex : signature :=
  {| Pred := pred_ex;
     arity := fun R => match R with Pe => 1 | Qe => 1 | Re2 => 2 end;
     Const := Empty_set |}.

(* D = {false, true}, F(P) = F(Q) = {true}, F(R) = ∅. *)
Definition M_bool : model Σ_ex :=
  @Build_model Σ_ex bool true (fun e : Empty_set => match e with end)
    (fun _ ds => match ds with [d] => d = true | _ => False end).

(* Variant with F(P) = {true} but F(Q) = {false}, for D29 and the
   non-reflexivity example. *)
Definition M_boolQ : model Σ_ex :=
  @Build_model Σ_ex bool true (fun e : Empty_set => match e with end)
    (fun R ds => match R, ds with
                 | Pe, [d] => d = true
                 | Qe, [d] => d = false
                 | _, _    => False
                 end).

(* One-element model, every atom true. *)
Definition M_one : model Σ_ex :=
  @Build_model Σ_ex unit tt (fun e : Empty_set => match e with end)
    (fun _ _ => True).

Definition Px : form Σ_ex := @Atom Σ_ex Pe [TVar 0].
Definition Qx : form Σ_ex := @Atom Σ_ex Qe [TVar 0].
Definition Py : form Σ_ex := @Atom Σ_ex Pe [TVar 1].

Definition g0 : G M_bool := fun _ => false.
Definition h1 : G M_bool := upd g0 0 true.

Lemma h1_0 : h1 0 = true.
Proof. apply upd_eq. Qed.

Lemma h1_neq_g0 : h1 <> g0.
Proof.
  intro E; apply (f_equal (fun f => f 0)) in E.
  rewrite h1_0 in E; discriminate E.
Qed.

(* ⟨g0, h1⟩ ∈ ⟦∃xPx⟧ in M_bool — the standard dynamic witness pair. *)
Lemma ex_px_g0_h1 : sem M_bool (Ex 0 Px) g0 h1.
Proof.
  exists h1; split; [apply dif_upd |].
  split; [reflexivity | simpl; rewrite h1_0; reflexivity].
Qed.

(* R4: the dynamic side of the static/dynamic distinction — ∃xPx is NOT a
   test (§3.2 remark after Def. 11, T 17 / P 57). *)
Theorem not_test_ex : ~ test (Ex 0 Px).
Proof.
  intro Ht; exact (h1_neq_g0 (Ht M_bool g0 h1 ex_px_g0_h1)).
Qed.

(* G&S 1991 §3.2, Fact 6, ⇒ direction REFUTED.  SOURCE NOTE: Fact 6 claims
   "φ is a test iff φ is either a condition or a contradiction" (T 17 /
   P 58); with identity in the language this is false:
   x = y ∧ ∃x[x = y] is a test (any output equals the input pointwise,
   hence Leibniz-equals it by extensionality [ARTIFACT-iv(a)]), but it is
   syntactically no condition and semantically no contradiction. *)
Theorem fact6_refuted : exists φ : form Σ_ex,
  test φ /\ ~ condition φ /\ ~ contradiction φ.
Proof.
  exists (Conj (Eq (TVar 0) (TVar 1)) (Ex 0 (Eq (TVar 0) (TVar 1)))).
  split; [| split].
  - (* a test *)
    intros M g h [k [[E1 He] [k' [Hd [E2 He']]]]]; subst k k'.
    simpl in He, He'.
    apply assign_ext; intro v.
    destruct (Nat.eq_dec v 0) as [-> | Hv].
    + rewrite He', (Hd 1); [rewrite <- He; reflexivity | discriminate].
    + apply Hd; exact Hv.
  - (* not a condition *)
    intro Hc; inversion Hc as [| | | | | | φ' ψ' Hc1 Hc2]; subst.
    inversion Hc2.
  - (* not a contradiction: true at the constant assignment in M_one *)
    intro Hc; apply (Hc M_one (fun _ => tt)).
    exists (fun _ => tt), (fun _ => tt); split.
    + split; reflexivity.
    + exists (fun _ => tt); split; [apply dif_refl | split; reflexivity].
Qed.

(* ========================================================================== *)
(*  Part 7 — Binding at the variable level (§3.3, Def. 15–16, T 18–19 /       *)
(*  P 58–61), Fact 9, the transfer lemma, Fact 8                              *)
(* ========================================================================== *)

(* Def. 16/15 compute the variable-level content of the occurrence-level
   Def. 13 [ARTIFACT-iv(b)]: at the level of variable sets the
   "de-activation" bookkeeping of aq/bp disappears (duplicates are
   harmless), giving the structural recursions below. *)

Definition term_vars {Σ} (t : term Σ) : list Var :=
  match t with TVar v => [v] | TCon _ => [] end.

(* V \ W as a computed list [ARTIFACT-v: in_dec on nat]. *)
Definition setminus (V W : list Var) : list Var :=
  filter (fun v => if in_dec Nat.eq_dec v W then false else true) V.

Lemma setminus_In : forall V W v, In v (setminus V W) <-> In v V /\ ~ In v W.
Proof.
  intros V W v; unfold setminus; rewrite filter_In.
  destruct (in_dec Nat.eq_dec v W); intuition congruence.
Qed.

(* Def. 16: x ∈ AQV(φ) iff ∃x has an active occurrence in φ.  Active
   occurrences survive only through conjunction and through ∃ itself
   (Def. 13 clauses 2–7): ¬, ∨, →, ∀ seal off all quantifiers. *)
Fixpoint AQV {Σ} (φ : form Σ) : list Var :=
  match φ with
  | Conj φ ψ => AQV φ ++ AQV ψ
  | Ex x φ   => x :: AQV φ
  | _        => []
  end.

(* Def. 15: x ∈ FV(φ) iff x has a free occurrence in φ.  In the ∧ and →
   clauses an occurrence in ψ is free only if not bound by an active
   quantifier of φ (Def. 13: binding pairs reach into the second conjunct
   and from antecedent to consequent). *)
Fixpoint FV {Σ} (φ : form Σ) : list Var :=
  match φ with
  | Atom _ ts => flat_map term_vars ts
  | Eq t1 t2  => term_vars t1 ++ term_vars t2
  | Neg φ     => FV φ
  | Conj φ ψ  => FV φ ++ setminus (FV ψ) (AQV φ)
  | Disj φ ψ  => FV φ ++ FV ψ
  | Impl φ ψ  => FV φ ++ setminus (FV ψ) (AQV φ)
  | Ex x φ    => remove Nat.eq_dec x (FV φ)
  | All x φ   => remove Nat.eq_dec x (FV φ)
  end.

Lemma In_FV_conj : forall Σ (φ ψ : form Σ) v,
  In v (FV (Conj φ ψ)) <-> In v (FV φ) \/ (In v (FV ψ) /\ ~ In v (AQV φ)).
Proof. intros; simpl; rewrite in_app_iff, setminus_In; reflexivity. Qed.

Lemma In_FV_impl : forall Σ (φ ψ : form Σ) v,
  In v (FV (Impl φ ψ)) <-> In v (FV φ) \/ (In v (FV ψ) /\ ~ In v (AQV φ)).
Proof. intros; simpl; rewrite in_app_iff, setminus_In; reflexivity. Qed.

Lemma In_FV_ex : forall Σ x (φ : form Σ) v,
  In v (FV (Ex x φ)) <-> In v (FV φ) /\ v <> x.
Proof.
  intros; simpl; split.
  - intro H; apply in_remove in H; exact H.
  - intros [H1 H2]; apply in_in_remove; auto.
Qed.

Lemma In_FV_all : forall Σ x (φ : form Σ) v,
  In v (FV (All x φ)) <-> In v (FV φ) /\ v <> x.
Proof.
  intros; simpl; split.
  - intro H; apply in_remove in H; exact H.
  - intros [H1 H2]; apply in_in_remove; auto.
Qed.

(* Term values depend only on the variables occurring in the term. *)
Lemma tval_agree : forall Σ (M : model Σ) (t : term Σ) (g g' : G M),
  agree (term_vars t) g g' -> tval M g t = tval M g' t.
Proof.
  intros Σ M t g g' H; destruct t; simpl.
  - apply H; left; reflexivity.
  - reflexivity.
Qed.

Lemma map_tval_agree : forall Σ (M : model Σ) (ts : list (term Σ)) (g g' : G M),
  agree (flat_map term_vars ts) g g' -> map (tval M g) ts = map (tval M g') ts.
Proof.
  intros Σ M ts g g' H; induction ts as [| t ts IH]; simpl; [reflexivity |].
  simpl in H; f_equal.
  - apply tval_agree; eapply agree_app_l; exact H.
  - apply IH; eapply agree_app_r; exact H.
Qed.

(* G&S 1991 §3.3, Fact 9 (T 19 / P 61), constructive form: an input-output
   pair can differ only on the actively quantified variables.  Induction on
   φ, generalising the assignments (design pitfall 9). *)
Theorem fact9 : forall Σ (φ : form Σ) (x : Var),
  ~ In x (AQV φ) ->
  forall M (g h : G M), sem M φ g h -> g x = h x.
Proof.
  intros Σ φ; induction φ as
    [R ts | t1 t2 | φ IH | φ1 IH1 φ2 IH2 | φ1 IH1 φ2 IH2 | φ1 IH1 φ2 IH2
    | y φ IH | y φ IH];
    intros x Hx M g h Hgh.
  - destruct Hgh as [E _]; subst h; reflexivity.
  - destruct Hgh as [E _]; subst h; reflexivity.
  - destruct Hgh as [E _]; subst h; reflexivity.
  - (* Conj *)
    destruct Hgh as [k [H1 H2]].
    simpl in Hx; rewrite in_app_iff in Hx.
    assert (Hx1 : ~ In x (AQV φ1)) by tauto.
    assert (Hx2 : ~ In x (AQV φ2)) by tauto.
    transitivity (k x).
    + exact (IH1 x Hx1 M g k H1).
    + exact (IH2 x Hx2 M k h H2).
  - destruct Hgh as [E _]; subst h; reflexivity.
  - destruct Hgh as [E _]; subst h; reflexivity.
  - (* Ex *)
    destruct Hgh as [k [Hd Hk]].
    simpl in Hx.
    assert (Hxy : x <> y) by (intro; subst; apply Hx; left; reflexivity).
    assert (HxA : ~ In x (AQV φ)) by (intro; apply Hx; right; assumption).
    transitivity (k x).
    + symmetry; apply Hd; exact Hxy.
    + exact (IH x HxA M k h Hk).
  - destruct Hgh as [E _]; subst h; reflexivity.
Qed.

(* Fact 9 in the source's contrapositive shape (constructive here: In on
   nat-lists is decidable [ARTIFACT-v]). *)
Corollary fact9_src : forall Σ (φ : form Σ) (x : Var) M (g h : G M),
  sem M φ g h -> g x <> h x -> In x (AQV φ).
Proof.
  intros Σ φ x M g h Hgh Hne.
  destruct (in_dec Nat.eq_dec x (AQV φ)) as [Hin | Hnin]; [exact Hin |].
  exfalso; apply Hne; eapply fact9; eauto.
Qed.

(* Corollary 9b: if no active quantifier of φ can bind a free variable of ψ,
   then processing φ leaves the free variables of ψ untouched — the step
   used verbatim in the source's proofs of Facts 13, 14, 16. *)
Corollary fact9_agree : forall Σ (φ ψ : form Σ) M (g h : G M),
  disjoint (AQV φ) (FV ψ) -> sem M φ g h -> agree (FV ψ) g h.
Proof.
  intros Σ φ ψ M g h Hdisj Hgh v Hv.
  eapply fact9; [| exact Hgh].
  intro HinA; exact (Hdisj v HinA Hv).
Qed.

(* The transfer lemma.  Not displayed in the source, but it is exactly the
   induction its proofs of Facts 8, 13, 14, 16 and the conditional laws of
   §3.4 run on: inputs that agree on FV(φ) produce outputs that agree on
   AQV(φ) and follow their respective inputs elsewhere.  The existential
   form survives the induction; the given-output form [transfer_given] is
   derived from it with extensionality. *)
Theorem transfer : forall Σ (φ : form Σ) M (g g' h : G M),
  agree (FV φ) g g' -> sem M φ g h ->
  exists h', sem M φ g' h' /\ agree (AQV φ) h' h /\
             (forall v, ~ In v (AQV φ) -> h' v = g' v).
Proof.
  intros Σ φ; induction φ as
    [R ts | t1 t2 | φ IH | φ1 IH1 φ2 IH2 | φ1 IH1 φ2 IH2 | φ1 IH1 φ2 IH2
    | y φ IH | y φ IH];
    intros M g g' h Hag Hgh.
  - (* Atom: the test passes at g' because the term values are unchanged *)
    destruct Hgh as [E HP]; subst h.
    exists g'; split; [| split].
    + split; [reflexivity |].
      replace (map (tval M g') ts) with (map (tval M g) ts); [exact HP |].
      apply map_tval_agree; exact Hag.
    + intros v [].
    + intros v _; reflexivity.
  - (* Eq *)
    destruct Hgh as [E HE]; subst h.
    exists g'; split; [| split].
    + split; [reflexivity |].
      assert (E1 : tval M g t1 = tval M g' t1)
        by (apply tval_agree; eapply agree_app_l; exact Hag).
      assert (E2 : tval M g t2 = tval M g' t2)
        by (apply tval_agree; eapply agree_app_r; exact Hag).
      simpl in HE; congruence.
    + intros v [].
    + intros v _; reflexivity.
  - (* Neg: a would-be witness at g' transfers back to g *)
    destruct Hgh as [E Hn]; subst h.
    exists g'; split; [| split].
    + split; [reflexivity |].
      intros [k Hk].
      apply Hn.
      destruct (IH M g' g k (agree_sym _ _ _ _ Hag) Hk) as [k' [Hk' _]].
      exists k'; exact Hk'.
    + intros v [].
    + intros v _; reflexivity.
  - (* Conj: chain the two IHs through the intermediate assignment *)
    destruct Hgh as [k [H1 H2]].
    assert (Hag1 : agree (FV φ1) g g')
      by (eapply agree_app_l; exact Hag).
    destruct (IH1 M g g' k Hag1 H1) as [k' [Hk' [Hagk Houtk]]].
    assert (Hagk2 : agree (FV φ2) k k').
    { intros v Hv.
      destruct (in_dec Nat.eq_dec v (AQV φ1)) as [Hin | Hnin].
      - symmetry; apply Hagk; exact Hin.
      - assert (Egg' : g v = g' v).
        { apply Hag; simpl; apply in_or_app; right; apply setminus_In; auto. }
        assert (Egk : g v = k v) by (eapply fact9; [exact Hnin | exact H1]).
        assert (Ek'g' : k' v = g' v) by (apply Houtk; exact Hnin).
        congruence. }
    destruct (IH2 M k k' h Hagk2 H2) as [h' [Hh' [Hagh Houth]]].
    exists h'; split; [| split].
    + exists k'; split; assumption.
    + intros v Hv; simpl in Hv; rewrite in_app_iff in Hv.
      destruct (in_dec Nat.eq_dec v (AQV φ2)) as [Hin2 | Hnin2].
      * apply Hagh; exact Hin2.
      * destruct Hv as [Hin1 | Hin2']; [| tauto].
        assert (E1 : h' v = k' v) by (apply Houth; exact Hnin2).
        assert (E2 : k' v = k v) by (apply Hagk; exact Hin1).
        assert (E3 : k v = h v) by (eapply fact9; [exact Hnin2 | exact H2]).
        congruence.
    + intros v Hv; simpl in Hv; rewrite in_app_iff in Hv.
      assert (E1 : h' v = k' v) by (apply Houth; tauto).
      assert (E2 : k' v = g' v) by (apply Houtk; tauto).
      congruence.
  - (* Disj: one IH per disjunct, both at the same test point *)
    destruct Hgh as [E Hd]; subst h.
    exists g'; split; [| split].
    + split; [reflexivity |].
      destruct Hd as [k [Hk | Hk]].
      * destruct (IH1 M g g' k (agree_app_l _ _ _ _ _ Hag) Hk) as [k' [Hk' _]].
        exists k'; left; exact Hk'.
      * destruct (IH2 M g g' k (agree_app_r _ _ _ _ _ Hag) Hk) as [k' [Hk' _]].
        exists k'; right; exact Hk'.
    + intros v [].
    + intros v _; reflexivity.
  - (* Impl: transfer an antecedent witness back, run the consequent, and
       transfer it forward *)
    destruct Hgh as [E Hi]; subst h.
    assert (Hag1 : agree (FV φ1) g g')
      by (eapply agree_app_l; exact Hag).
    exists g'; split; [| split].
    + split; [reflexivity |].
      intros k' Hk'.
      destruct (IH1 M g' g k' (agree_sym _ _ _ _ Hag1) Hk')
        as [k [Hk [Hagk Houtk]]].
      destruct (Hi k Hk) as [j Hj].
      assert (Hagk2 : agree (FV φ2) k k').
      { intros v Hv.
        destruct (in_dec Nat.eq_dec v (AQV φ1)) as [Hin | Hnin].
        - apply Hagk; exact Hin.
        - assert (Ekg : k v = g v) by (apply Houtk; exact Hnin).
          assert (Egg' : g v = g' v).
          { apply Hag; simpl; apply in_or_app; right; apply setminus_In; auto. }
          assert (Eg'k' : g' v = k' v)
            by (eapply fact9; [exact Hnin | exact Hk']).
          congruence. }
      destruct (IH2 M k k' j Hagk2 Hj) as [j' [Hj' _]].
      exists j'; exact Hj'.
    + intros v [].
    + intros v _; reflexivity.
  - (* Ex: re-set y at g' to the value the g-side witness chose *)
    destruct Hgh as [k [Hd Hk]].
    set (k' := upd g' y (k y)).
    assert (Hagk : agree (FV φ) k k').
    { intros v Hv.
      destruct (Nat.eq_dec v y) as [-> | Hvy].
      - unfold k'; rewrite upd_eq; reflexivity.
      - unfold k'; rewrite upd_neq; [| exact Hvy].
        assert (Ekg : k v = g v) by (apply Hd; exact Hvy).
        assert (Egg' : g v = g' v)
          by (apply Hag; simpl; apply in_in_remove; auto).
        congruence. }
    destruct (IH M k k' h Hagk Hk) as [h' [Hh' [Hagh Houth]]].
    exists h'; split; [| split].
    + exists k'; split; [unfold k'; apply dif_upd | exact Hh'].
    + intros v Hv; simpl in Hv.
      destruct (in_dec Nat.eq_dec v (AQV φ)) as [Hin | Hnin].
      * apply Hagh; exact Hin.
      * destruct Hv as [Evy | Hin']; [| tauto].
        subst v.
        assert (E1 : h' y = k' y) by (apply Houth; exact Hnin).
        assert (E2 : k' y = k y) by (unfold k'; apply upd_eq).
        assert (E3 : k y = h y) by (eapply fact9; [exact Hnin | exact Hk]).
        congruence.
    + intros v Hv; simpl in Hv.
      assert (Hvy : v <> y) by (intro; subst; apply Hv; left; reflexivity).
      assert (HvA : ~ In v (AQV φ)) by (intro; apply Hv; right; assumption).
      assert (E1 : h' v = k' v) by (apply Houth; exact HvA).
      assert (E2 : k' v = g' v) by (unfold k'; apply upd_neq; exact Hvy).
      congruence.
  - (* All: a g'-side y-variant is matched by the corresponding g-side
       y-variant, and the continuation transfers *)
    destruct Hgh as [E Ha]; subst h.
    exists g'; split; [| split].
    + split; [reflexivity |].
      intros k' Hd'.
      set (k := upd g y (k' y)).
      destruct (Ha k) as [j Hj]; [unfold k; apply dif_upd |].
      assert (Hagk : agree (FV φ) k k').
      { intros v Hv.
        destruct (Nat.eq_dec v y) as [-> | Hvy].
        - unfold k; rewrite upd_eq; reflexivity.
        - unfold k; rewrite upd_neq; [| exact Hvy].
          assert (Egg' : g v = g' v)
            by (apply Hag; simpl; apply in_in_remove; auto).
          assert (Ek'g' : k' v = g' v) by (apply Hd'; exact Hvy).
          congruence. }
      destruct (IH M k k' j Hagk Hj) as [j' [Hj' _]].
      exists j'; exact Hj'.
    + intros v [].
    + intros v _; reflexivity.
Qed.

(* G&S 1991 §3.3, Fact 8 (T 19 / P 61): truth depends only on the free
   variables. *)
Theorem fact8 : forall Σ (φ : form Σ) M (g h : G M),
  agree (FV φ) g h -> (true_wrt M φ g <-> true_wrt M φ h).
Proof.
  intros Σ φ M g h Hag; split; intros [k Hk].
  - destruct (transfer Σ φ M g h k Hag Hk) as [k' [Hk' _]].
    exists k'; exact Hk'.
  - destruct (transfer Σ φ M h g k (agree_sym _ _ _ _ Hag) Hk) as [k' [Hk' _]].
    exists k'; exact Hk'.
Qed.

(* The given-output form of the transfer lemma (needs extensionality
   [ARTIFACT-iv(a)]: the prescribed output must be Leibniz-equal to the
   produced one).  Used by D32, D33, D47. *)
Lemma transfer_given : forall Σ (φ : form Σ) M (g g' h h' : G M),
  agree (FV φ) g g' -> sem M φ g h ->
  agree (AQV φ) h' h -> (forall v, ~ In v (AQV φ) -> h' v = g' v) ->
  sem M φ g' h'.
Proof.
  intros Σ φ M g g' h h' Hag Hgh Hagh Hout.
  destruct (transfer Σ φ M g g' h Hag Hgh) as [h'' [Hh'' [Hagh'' Hout'']]].
  replace h' with h''; [exact Hh'' |].
  apply assign_ext; intro v.
  destruct (in_dec Nat.eq_dec v (AQV φ)) as [Hin | Hnin].
  - rewrite (Hagh'' v Hin); symmetry; apply Hagh; exact Hin.
  - rewrite (Hout'' v Hnin); symmetry; apply Hout; exact Hnin.
Qed.

(* ========================================================================== *)
(*  Part 8 — The laws of §3.4 (T 20–25 / P 61–66).  D-numbers follow the      *)
(*  design document's reading-order numbering of the unnumbered displays.     *)
(* ========================================================================== *)

(* Relation-level helpers.  The unconditional laws that hold for arbitrary
   relations are proved here once and instantiated below. *)

Lemma rcomp_assoc : forall A (R S T : Rel A),
  rel_eq (rcomp (rcomp R S) T) (rcomp R (rcomp S T)).
Proof.
  intros A R S T g h; split.
  - intros [k [[m [H1 H2]] H3]]; exists m; split; [exact H1 | exists k; auto].
  - intros [m [H1 [k [H2 H3]]]]; exists k; split; [exists m; auto | exact H3].
Qed.

(* Egli's Theorem at relation level: random assignment followed by R, then
   S, is random assignment followed by (R then S). *)
Lemma rcomp_rex : forall D (x : Var) (R S : Rel (Assign D)),
  rel_eq (rcomp (rex x R) S) (rex x (rcomp R S)).
Proof.
  intros D x R S g h; split.
  - intros [k [[m [Hd Hm]] Hk]]; exists m; split; [exact Hd | exists k; auto].
  - intros [m [Hd [k [Hm Hk]]]]; exists k; split; [exists m; auto | exact Hk].
Qed.

(* Egli's Corollary at relation level. *)
Lemma rimpl_rex : forall D (x : Var) (R S : Rel (Assign D)),
  rel_eq (rimpl (rex x R) S) (rall x (rimpl R S)).
Proof.
  intros D x R S g h; split.
  - intros [-> HC]; split; [reflexivity |].
    intros m Hd; exists m; split; [reflexivity |].
    intros k Hk; apply HC; exists m; auto.
  - intros [-> HC]; split; [reflexivity |].
    intros k [m [Hd Hm]].
    destruct (HC m Hd) as [j [-> Hj]]; exact (Hj k Hm).
Qed.

(* Two rtest-shaped relations compose commutatively and idempotently. *)
Lemma rcomp_rtest_comm : forall A (P Q : A -> Prop),
  rel_eq (rcomp (rtest P) (rtest Q)) (rcomp (rtest Q) (rtest P)).
Proof.
  intros A P Q g h; split;
    intros [k [[E1 H1] [E2 H2]]]; subst;
    exists g; repeat split; assumption.
Qed.

Lemma rtest_dup : forall A (P : A -> Prop),
  rel_eq (rtest P) (rcomp (rtest P) (rtest P)).
Proof.
  intros A P g h; split.
  - intros [-> HP]; exists g; repeat split; assumption.
  - intros [k [[E1 H1] [E2 H2]]]; subst; split; [reflexivity | assumption].
Qed.

Lemma rclos_congr : forall A (R S : Rel A),
  rel_eq R S -> rel_eq (rclos R) (rclos S).
Proof.
  intros A R S H g h; split; intros [-> [k Hk]];
    (split; [reflexivity |]); exists k; apply (H g k); exact Hk.
Qed.

Lemma rneg_congr : forall A (R S : Rel A),
  rel_eq R S -> rel_eq (rneg R) (rneg S).
Proof.
  intros A R S H g h; split; intros [-> Hn];
    (split; [reflexivity |]); intros [k Hk]; apply Hn; exists k;
    apply (H g k); exact Hk.
Qed.

Lemma rclos_rclos : forall A (R : Rel A), rel_eq (rclos (rclos R)) (rclos R).
Proof.
  intros A R g h; split.
  - intros [-> [k [-> [m Hm]]]]; split; [reflexivity | exists m; exact Hm].
  - intros [-> [m Hm]]; split; [reflexivity |].
    exists g; split; [reflexivity | exists m; exact Hm].
Qed.

Lemma rclos_rneg : forall A (R : Rel A), rel_eq (rclos (rneg R)) (rneg R).
Proof.
  intros A R g h; split.
  - intros [-> [k [-> Hn]]]; split; [reflexivity | exact Hn].
  - intros [-> Hn]; split; [reflexivity |].
    exists g; split; [reflexivity | exact Hn].
Qed.

Lemma rneg_rclos : forall A (R : Rel A), rel_eq (rneg (rclos R)) (rneg R).
Proof.
  intros A R g h; split; intros [-> Hn]; (split; [reflexivity |]).
  - intros [k Hk]; apply Hn; exists g; split; [reflexivity | exists k; exact Hk].
  - intros [k [-> Hs]]; exact (Hn Hs).
Qed.

(* -------------------------------------------------------------------------- *)
(*  Interdefinability and its limits (T 20–21 / P 61–62)                       *)
(* -------------------------------------------------------------------------- *)

(* G&S 1991 §3.4 T 20 / P 61, D1: φ → ψ ≃ ¬[φ ∧ ¬ψ]. *)
Theorem d1 : forall Σ (φ ψ : form Σ), equiv (φ →' ψ)%dpl (¬' (φ ∧' ¬' ψ))%dpl.
Proof.
  intros Σ φ ψ M g h; simpl; unfold rimpl, rneg, rcomp, rtest; split.
  - intros [-> HC]; split; [reflexivity |].
    intros [k [m [Hm [-> Hn]]]].
    destruct (HC m Hm) as [j Hj]; apply Hn; exists j; exact Hj.
  - intros [-> HN]; split; [reflexivity |].
    intros k Hk.
    apply NNPP; intro Hno.
    apply HN; exists k, k; split; [exact Hk |].
    split; [reflexivity | exact Hno].
Qed.

(* G&S 1991 §3.4 T 20 / P 61, D2: φ ∨ ψ ≃ ¬[¬φ ∧ ¬ψ]. *)
Theorem d2 : forall Σ (φ ψ : form Σ), equiv (φ ∨' ψ)%dpl (¬' ((¬' φ) ∧' (¬' ψ)))%dpl.
Proof.
  intros Σ φ ψ M g h; simpl; unfold rdisj, rneg, rcomp, rtest; split.
  - intros [-> [k [Hk | Hk]]]; (split; [reflexivity |]);
      intros [k' [m [[-> Hn1] [-> Hn2]]]].
    + apply Hn1; exists k; exact Hk.
    + apply Hn2; exists k; exact Hk.
  - intros [-> HN]; split; [reflexivity |].
    destruct (classic (exists k, sem M φ g k)) as [[k Hk] | Hno1].
    + exists k; left; exact Hk.
    + destruct (classic (exists k, sem M ψ g k)) as [[k Hk] | Hno2].
      * exists k; right; exact Hk.
      * exfalso; apply HN.
        exists g, g; repeat split; assumption.
Qed.

(* G&S 1991 §3.4 T 20 / P 61, D3: ∀xφ ≃ ¬∃x¬φ. *)
Theorem d3 : forall Σ x (φ : form Σ), equiv (∀' x , φ)%dpl (¬' (∃' x , (¬' φ)))%dpl.
Proof.
  intros Σ x φ M g h; simpl; unfold rall, rex, rneg, rtest; split.
  - intros [-> HC]; split; [reflexivity |].
    intros [k [m [Hd [-> Hn]]]].
    destruct (HC m Hd) as [j Hj]; apply Hn; exists j; exact Hj.
  - intros [-> HN]; split; [reflexivity |].
    intros k Hd.
    apply NNPP; intro Hno.
    apply HN; exists k, k; split; [exact Hd |].
    split; [reflexivity | exact Hno].
Qed.

(* G&S 1991 §3.4 T 21 / P 62, D7: φ ∧ ψ ≃s ¬[φ → ¬ψ] — the s-equivalence
   half of the failed interdefinability D4. *)
Theorem d7 : forall Σ (φ ψ : form Σ), s_equiv (φ ∧' ψ)%dpl (¬' (φ →' ¬' ψ))%dpl.
Proof.
  intros Σ φ ψ M g; split.
  - intros [h [k [H1 H2]]].
    exists g; split; [reflexivity |].
    intros [j [-> HC]].
    destruct (HC k H1) as [m [-> Hn]]; apply Hn; exists h; exact H2.
  - intros [h [-> HN]].
    apply NNPP; intro Hno.
    apply HN; exists g; split; [reflexivity |].
    intros k Hk; exists k; split; [reflexivity |].
    intros [j Hj]; apply Hno; exists j, k; auto.
Qed.

(* G&S 1991 §3.4 T 21 / P 62, D9: ∃xφ ≃s ¬∀x¬φ. *)
Theorem d9 : forall Σ x (φ : form Σ), s_equiv (∃' x , φ)%dpl (¬' (∀' x , (¬' φ)))%dpl.
Proof.
  intros Σ x φ M g; split.
  - intros [h [k [Hd Hk]]].
    exists g; split; [reflexivity |].
    intros [j [-> HC]].
    destruct (HC k Hd) as [m [-> Hn]]; apply Hn; exists h; exact Hk.
  - intros [h [-> HN]].
    apply NNPP; intro Hno.
    apply HN; exists g; split; [reflexivity |].
    intros k Hd; exists k; split; [reflexivity |].
    intros [j Hj]; apply Hno; exists j, k; auto.
Qed.

(* G&S 1991 §3.4 T 21 / P 62, D10: φ ∨ ψ ≃ ¬φ → ψ (disjunction is definable
   from implication; the converse D11 fails, see Part 9). *)
Theorem d10 : forall Σ (φ ψ : form Σ), equiv (φ ∨' ψ)%dpl ((¬' φ) →' ψ)%dpl.
Proof.
  intros Σ φ ψ M g h; simpl; unfold rdisj, rimpl, rneg, rtest; split.
  - intros [-> [k [Hk | Hk]]]; (split; [reflexivity |]); intros m [-> Hn].
    + exfalso; apply Hn; exists k; exact Hk.
    + exists k; exact Hk.
  - intros [-> HC]; split; [reflexivity |].
    destruct (classic (exists k, sem M φ g k)) as [[k Hk] | Hno].
    + exists k; left; exact Hk.
    + destruct (HC g (conj eq_refl Hno)) as [k Hk].
      exists k; right; exact Hk.
Qed.

(* G&S 1991 §3.4 T 21 / P 62, D16: ¬∃xφ ≃ ∀x¬φ — this quantifier
   interdefinability holds unconditionally ("negation turns anything into
   a test").  Constructive. *)
Theorem d16 : forall Σ x (φ : form Σ), equiv (¬' (∃' x , φ))%dpl (∀' x , (¬' φ))%dpl.
Proof.
  intros Σ x φ M g h; simpl; unfold rall, rex, rneg, rtest; split.
  - intros [-> HN]; split; [reflexivity |].
    intros k Hd; exists k; split; [reflexivity |].
    intros [j Hj]; apply HN; exists j, k; auto.
  - intros [-> HC]; split; [reflexivity |].
    intros [j [k [Hd Hk]]].
    destruct (HC k Hd) as [m [-> Hn]]; apply Hn; exists j; exact Hk.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Double negation and closure (T 22 / P 62–63)                               *)
(* -------------------------------------------------------------------------- *)

(* G&S 1991 §3.4 T 22 / P 62, D17: φ ≃s ¬¬φ — double negation preserves
   truth conditions (but not meaning: see negneg_witness in Part 9). *)
Theorem d17 : forall Σ (φ : form Σ), s_equiv φ (¬' ¬' φ)%dpl.
Proof.
  intros Σ φ M g; split.
  - intros [h Hh].
    exists g; split; [reflexivity |].
    intros [k [-> Hn]]; apply Hn; exists h; exact Hh.
  - intros [h [-> HN]].
    apply NNPP; intro Hno.
    apply HN; exists g; split; [reflexivity |].
    intros [k Hk]; apply Hno; exists k; exact Hk.
Qed.

(* G&S 1991 §3.4 T 22 / P 62, D18: ¬¬φ ≃ φ iff φ is a test — the law of
   double negation holds exactly for the static formulas.  The concrete
   counterexample ¬¬∃xPx ≄ ∃xPx is negneg_witness / negneg_not_equiv
   (Part 9). *)
Theorem d18 : forall Σ (φ : form Σ), equiv (¬' ¬' φ)%dpl φ <-> test φ.
Proof.
  intros Σ φ; split.
  - (* ¬¬φ ≃ φ makes φ a test, ¬¬φ being one *)
    intros He M g h Hgh.
    assert (Hnn : sem M (¬' ¬' φ)%dpl g h) by (apply He; exact Hgh).
    destruct Hnn as [E _]; exact E.
  - intros Ht M g h; split.
    + intros [-> HN].
      assert (Hs : exists j, sem M φ g j).
      { apply NNPP; intro Hno.
        apply HN; exists g; split; [reflexivity | exact Hno]. }
      destruct Hs as [j Hj].
      assert (E := Ht M g j Hj); subst j.
      exact Hj.
    + intros Hgh.
      assert (E := Ht M g h Hgh); subst h.
      split; [reflexivity |].
      intros [k [-> Hn]]; apply Hn; exists g; exact Hgh.
Qed.

(* G&S 1991 §3.4 T 22 / P 63, D19: ♦φ ≃ ¬¬φ (definitional for the surrogate)
   and ♦φ ≃ φ iff φ is a test. *)
Theorem d19_clos_def : forall Σ (φ : form Σ), equiv (Clos φ) (¬' ¬' φ)%dpl.
Proof. intros Σ φ; apply equiv_refl. Qed.

Theorem d19_test : forall Σ (φ : form Σ), equiv (Clos φ) φ <-> test φ.
Proof. intros Σ φ; exact (d18 Σ φ). Qed.

(* G&S 1991 §3.4 T 22 / P 63, D20: ♦φ ≃ ♦ψ ⇔ φ ≃s ψ — closure keeps exactly
   the truth-conditional content. *)
Theorem d20 : forall Σ (φ ψ : form Σ),
  equiv (Clos φ) (Clos ψ) <-> s_equiv φ ψ.
Proof.
  intros Σ φ ψ; split.
  - intros He M g; split.
    + intros [h Hh].
      assert (Hcl : sem M (Clos φ) g g).
      { split; [reflexivity |].
        intros [k [-> Hn]]; apply Hn; exists h; exact Hh. }
      destruct (proj1 (He M g g) Hcl) as [_ Hnn].
      apply NNPP; intro Hno.
      apply Hnn; exists g; split; [reflexivity | exact Hno].
    + intros [h Hh].
      assert (Hcl : sem M (Clos ψ) g g).
      { split; [reflexivity |].
        intros [k [-> Hn]]; apply Hn; exists h; exact Hh. }
      destruct (proj2 (He M g g) Hcl) as [_ Hnn].
      apply NNPP; intro Hno.
      apply Hnn; exists g; split; [reflexivity | exact Hno].
  - intros Hs M g h; split.
    + intros [-> Hn]; split; [reflexivity |].
      intros [k [-> Hn2]].
      apply Hn; exists g; split; [reflexivity |].
      intros [m Hm]; apply Hn2.
      apply (proj1 (Hs M g)); exists m; exact Hm.
    + intros [-> Hn]; split; [reflexivity |].
      intros [k [-> Hn2]].
      apply Hn; exists g; split; [reflexivity |].
      intros [m Hm]; apply Hn2.
      apply (proj2 (Hs M g)); exists m; exact Hm.
Qed.

(* G&S 1991 §3.4 T 22 / P 63, D21: ♦♦φ ≃ ♦φ. *)
Theorem d21 : forall Σ (φ : form Σ), equiv (Clos (Clos φ)) (Clos φ).
Proof.
  intros Σ φ M.
  eapply rel_eq_trans; [apply sem_clos |].
  eapply rel_eq_trans; [apply rclos_congr; apply sem_clos |].
  eapply rel_eq_trans; [apply rclos_rclos |].
  apply rel_eq_sym; apply sem_clos.
Qed.

(* G&S 1991 §3.4 T 22 / P 63, D22: ♦¬φ ≃ ¬φ ≃ ¬♦φ. *)
Theorem d22_left : forall Σ (φ : form Σ), equiv (Clos (¬' φ))%dpl (¬' φ)%dpl.
Proof.
  intros Σ φ M.
  eapply rel_eq_trans; [apply sem_clos |]; apply rclos_rneg.
Qed.

Theorem d22_right : forall Σ (φ : form Σ), equiv (¬' φ)%dpl (¬' (Clos φ))%dpl.
Proof.
  intros Σ φ M; apply rel_eq_sym.
  eapply rel_eq_trans; [apply rneg_congr; apply sem_clos |].
  apply rneg_rclos.
Qed.

(* G&S 1991 §3.4 T 22 / P 63, D23: ♦[φ ∧ ψ] ≃ ¬[φ → ¬ψ] — the restricted
   version of the failed interdefinability D4. *)
Theorem d23 : forall Σ (φ ψ : form Σ), equiv (Clos (φ ∧' ψ))%dpl (¬' (φ →' ¬' ψ))%dpl.
Proof.
  intros Σ φ ψ M g h; split.
  - intro H; apply (proj1 (sem_clos Σ M (φ ∧' ψ)%dpl g h)) in H.
    destruct H as [-> [k [m [H1 H2]]]].
    split; [reflexivity |].
    intros [j [-> HC]].
    destruct (HC m H1) as [j' [-> Hn]]; apply Hn; exists k; exact H2.
  - intros [-> HN].
    apply (proj2 (sem_clos Σ M (φ ∧' ψ)%dpl g g)).
    split; [reflexivity |].
    apply NNPP; intro Hno.
    apply HN; exists g; split; [reflexivity |].
    intros k Hk; exists k; split; [reflexivity |].
    intros [j Hj]; apply Hno; exists j, k; auto.
Qed.

(* G&S 1991 §3.4 T 22 / P 63, D24: ♦φ ∧ ♦ψ ≃ ¬[¬φ ∨ ¬ψ] (restricted D5).
   Constructive: both sides stay under the negations. *)
Theorem d24 : forall Σ (φ ψ : form Σ),
  equiv ((Clos φ) ∧' (Clos ψ))%dpl (¬' ((¬' φ) ∨' (¬' ψ)))%dpl.
Proof.
  intros Σ φ ψ M g h; split.
  - intros [k [[-> Hn1] [-> Hn2]]].
    split; [reflexivity |].
    intros [k' [-> [m [Hm | Hm]]]].
    + apply Hn1; exists m; exact Hm.
    + apply Hn2; exists m; exact Hm.
  - intros [-> HN].
    exists g; split; (split; [reflexivity |]); intros [m Hm].
    + apply HN; exists g; split; [reflexivity |]; exists m; left; exact Hm.
    + apply HN; exists g; split; [reflexivity |]; exists m; right; exact Hm.
Qed.

(* G&S 1991 §3.4 T 22 / P 63, D25: ♦∃xφ ≃ ¬∀x¬φ (restricted D6).
   Constructive. *)
Theorem d25 : forall Σ x (φ : form Σ),
  equiv (Clos (∃' x , φ))%dpl (¬' (∀' x , (¬' φ)))%dpl.
Proof.
  intros Σ x φ M g h; split.
  - intros [-> Hn].
    split; [reflexivity |].
    intros [k [-> HC]].
    apply Hn; exists g; split; [reflexivity |].
    intros [j [m [Hd Hm]]].
    destruct (HC m Hd) as [j' [-> Hn']]; apply Hn'; exists j; exact Hm.
  - intros [-> HN].
    split; [reflexivity |].
    intros [k [-> Hn]].
    apply HN; exists g; split; [reflexivity |].
    intros m Hd; exists m; split; [reflexivity |].
    intros [j Hj]; apply Hn; exists j, m; auto.
Qed.

(* G&S 1991 §3.4 T 22 / P 63, D26: ♦φ → ψ ≃ ¬φ ∨ ψ (restricted D11). *)
Theorem d26 : forall Σ (φ ψ : form Σ),
  equiv ((Clos φ) →' ψ)%dpl ((¬' φ) ∨' ψ)%dpl.
Proof.
  intros Σ φ ψ M g h; split.
  - intros [-> HC]; split; [reflexivity |].
    destruct (classic (exists k, sem M φ g k)) as [[k Hk] | Hno].
    + assert (Hcl : sem M (Clos φ) g g).
      { split; [reflexivity |].
        intros [m [-> Hn]]; apply Hn; exists k; exact Hk. }
      destruct (HC g Hcl) as [j Hj].
      exists j; right; exact Hj.
    + exists g; left; split; [reflexivity | exact Hno].
  - intros [-> [k [[-> Hn] | Hk]]]; (split; [reflexivity |]); intros m [-> Hnn].
    + exfalso; apply Hnn; exists g; split; [reflexivity | exact Hn].
    + exists k; exact Hk.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Conjunction (T 22–23 / P 63–64)                                            *)
(* -------------------------------------------------------------------------- *)

(* G&S 1991 §3.4 T 22 / P 63, D27: [φ ∧ ψ] ∧ χ ≃ φ ∧ [ψ ∧ χ] — conjunction
   is associative "despite the increased binding power of the existential
   quantifier".  Constructive, axiom-free. *)
Theorem d27_conj_assoc : forall Σ (φ ψ χ : form Σ),
  equiv ((φ ∧' ψ) ∧' χ)%dpl (φ ∧' (ψ ∧' χ))%dpl.
Proof. intros Σ φ ψ χ M; apply rcomp_assoc. Qed.

(* G&S 1991 §3.4 T 23 / P 64, D30: ♦φ ∧ ♦ψ ≃ ♦ψ ∧ ♦φ — commutativity holds
   for closures.  Constructive. *)
Theorem d30 : forall Σ (φ ψ : form Σ),
  equiv ((Clos φ) ∧' (Clos ψ))%dpl ((Clos ψ) ∧' (Clos φ))%dpl.
Proof. intros Σ φ ψ M; apply rcomp_rtest_comm. Qed.

(* G&S 1991 §3.4 T 23 / P 64, D31: ♦φ ≃ ♦φ ∧ ♦φ — idempotency holds for
   closures.  Constructive. *)
Theorem d31 : forall Σ (φ : form Σ),
  equiv (Clos φ) ((Clos φ) ∧' (Clos φ))%dpl.
Proof. intros Σ φ M; apply rtest_dup. Qed.

(* G&S 1991 §3.4 T 23 / P 64, D32: AQV(φ) ∩ FV(φ) = ∅ ⇒ φ ≃ φ ∧ φ —
   conditional idempotency of conjunction.  Uses the given-output transfer
   lemma, hence extensionality [ARTIFACT-iv(a)]. *)
Theorem d32 : forall Σ (φ : form Σ),
  disjoint (AQV φ) (FV φ) -> equiv φ (φ ∧' φ)%dpl.
Proof.
  intros Σ φ Hdisj M g h; split.
  - intro Hgh.
    exists h; split; [exact Hgh |].
    apply (transfer_given Σ φ M g h h h).
    + eapply fact9_agree; [exact Hdisj | exact Hgh].
    + exact Hgh.
    + apply agree_refl.
    + intros v _; reflexivity.
  - intros [k [H1 H2]].
    apply (transfer_given Σ φ M k g h h).
    + apply agree_sym; eapply fact9_agree; [exact Hdisj | exact H1].
    + exact H2.
    + apply agree_refl.
    + intros v Hv.
      assert (E1 : k v = h v) by (eapply fact9; [exact Hv | exact H2]).
      assert (E2 : g v = k v) by (eapply fact9; [exact Hv | exact H1]).
      congruence.
Qed.

(* G&S 1991 §3.4 T 23 / P 64, D33: if AQV(φ) ∩ FV(ψ) = AQV(ψ) ∩ FV(φ) =
   AQV(φ) ∩ AQV(ψ) = ∅ then φ ∧ ψ ≃ ψ ∧ φ — conditional commutativity
   ("commuting the conjuncts does not change the binding pairs"). *)
Lemma d33_half : forall Σ (φ ψ : form Σ) M (g h : G M),
  disjoint (AQV φ) (FV ψ) -> disjoint (AQV ψ) (FV φ) ->
  disjoint (AQV φ) (AQV ψ) ->
  sem M (φ ∧' ψ)%dpl g h -> sem M (ψ ∧' φ)%dpl g h.
Proof.
  intros Σ φ ψ M g h H1 H2 H3 [k [Hφ Hψ]].
  assert (Hag0 : agree (FV ψ) g k)
    by (eapply fact9_agree; [exact H1 | exact Hφ]).
  destruct (transfer Σ ψ M k g h (agree_sym _ _ _ _ Hag0) Hψ)
    as [m [Hm [Hagm Houtm]]].
  exists m; split; [exact Hm |].
  apply (transfer_given Σ φ M g m k h).
  - (* agree (FV φ) g m *)
    intros v Hv.
    assert (HvA : ~ In v (AQV ψ)) by (intro Hin; exact (H2 v Hin Hv)).
    symmetry; apply Houtm; exact HvA.
  - exact Hφ.
  - (* agree (AQV φ) h k *)
    intros v Hv.
    assert (HvA : ~ In v (AQV ψ)) by (intro Hin; exact (H3 v Hv Hin)).
    symmetry; exact (fact9 Σ ψ v HvA M k h Hψ).
  - (* outside AQV(φ) the output follows m *)
    intros v Hv.
    destruct (in_dec Nat.eq_dec v (AQV ψ)) as [Hin | Hnin].
    + symmetry; apply Hagm; exact Hin.
    + assert (E1 : k v = h v) by (exact (fact9 Σ ψ v Hnin M k h Hψ)).
      assert (E2 : g v = k v) by (exact (fact9 Σ φ v Hv M g k Hφ)).
      assert (E3 : m v = g v) by (apply Houtm; exact Hnin).
      congruence.
Qed.

Lemma disjoint_sym : forall V W, disjoint V W -> disjoint W V.
Proof. intros V W H v Hv Hw; exact (H v Hw Hv). Qed.

Theorem d33 : forall Σ (φ ψ : form Σ),
  disjoint (AQV φ) (FV ψ) -> disjoint (AQV ψ) (FV φ) ->
  disjoint (AQV φ) (AQV ψ) ->
  equiv (φ ∧' ψ)%dpl (ψ ∧' φ)%dpl.
Proof.
  intros Σ φ ψ H1 H2 H3 M g h; split.
  - apply d33_half; assumption.
  - apply d33_half; [exact H2 | exact H1 | apply disjoint_sym; exact H3].
Qed.

(* -------------------------------------------------------------------------- *)
(*  Disjunction (T 23–24 / P 64) — and the printed idempotency law            *)
(* -------------------------------------------------------------------------- *)

(* SOURCE NOTE on D34.  The display "φ ≃ φ ∨ φ" (T 23 / P 64: "disjunction
   ... is unconditionally idempotent") is FALSE as printed: by Def. 2
   clause 5, φ ∨ φ is a test — indeed φ ∨ φ ≃ ♦φ — so the law fails for any
   non-test φ (concretely for ∃xPx: d34_refuted, Part 9).  What does hold:
   the closure law ♦φ ≃ φ ∨ φ, the s-equivalence φ ≃s φ ∨ φ (the source's
   intended "no anaphoric relations across disjuncts" content), and the
   equivalence itself for tests. *)
Theorem d34_clos : forall Σ (φ : form Σ), equiv (Clos φ) (φ ∨' φ)%dpl.
Proof.
  intros Σ φ M g h; split.
  - intros [-> Hn]; split; [reflexivity |].
    assert (Hs : exists k, sem M φ g k).
    { apply NNPP; intro Hno.
      apply Hn; exists g; split; [reflexivity | exact Hno]. }
    destruct Hs as [k Hk]; exists k; left; exact Hk.
  - intros [-> [k [Hk | Hk]]]; (split; [reflexivity |]);
      intros [m [-> Hn]]; apply Hn; exists k; exact Hk.
Qed.

Theorem d34_s_equiv : forall Σ (φ : form Σ), s_equiv φ (φ ∨' φ)%dpl.
Proof.
  intros Σ φ M g; split.
  - intros [h Hh].
    exists g; split; [reflexivity | exists h; left; exact Hh].
  - intros [h [-> [k [Hk | Hk]]]]; exists k; exact Hk.
Qed.

Theorem d34_test : forall Σ (φ : form Σ), test φ -> equiv φ (φ ∨' φ)%dpl.
Proof.
  intros Σ φ Ht M g h; split.
  - intro Hgh.
    assert (E := Ht M g h Hgh); subst h.
    split; [reflexivity | exists g; left; exact Hgh].
  - intros [-> [k [Hk | Hk]]];
      assert (E := Ht M g k Hk); subst k; exact Hk.
Qed.

(* G&S 1991 §3.4 T 24 / P 64, D35: φ ∨ ψ ≃ ψ ∨ φ.  Constructive. *)
Theorem d35 : forall Σ (φ ψ : form Σ), equiv (φ ∨' ψ)%dpl (ψ ∨' φ)%dpl.
Proof.
  intros Σ φ ψ M g h; split;
    intros [-> [k [Hk | Hk]]]; (split; [reflexivity |]); exists k;
    solve [ right; exact Hk | left; exact Hk ].
Qed.

(* G&S 1991 §3.4 T 24 / P 64, D36: φ ∨ [ψ ∨ χ] ≃ [φ ∨ ψ] ∨ χ.
   Constructive. *)
Theorem d36 : forall Σ (φ ψ χ : form Σ),
  equiv (φ ∨' (ψ ∨' χ))%dpl ((φ ∨' ψ) ∨' χ)%dpl.
Proof.
  intros Σ φ ψ χ M g h; split.
  - intros [-> [k [Hk | [-> [m [Hm | Hm]]]]]]; (split; [reflexivity |]).
    + exists g; left; split; [reflexivity | exists k; left; exact Hk].
    + exists g; left; split; [reflexivity | exists m; right; exact Hm].
    + exists m; right; exact Hm.
  - intros [-> [k [[-> [m [Hm | Hm]]] | Hk]]]; (split; [reflexivity |]).
    + exists m; left; exact Hm.
    + exists g; right; split; [reflexivity | exists m; left; exact Hm].
    + exists g; right; split; [reflexivity | exists k; right; exact Hk].
Qed.

(* -------------------------------------------------------------------------- *)
(*  De Morgan-style distribution (T 24 / P 64)                                 *)
(* -------------------------------------------------------------------------- *)

(* G&S 1991 §3.4 T 24 / P 64, D37: ♦[φ ∧ [ψ ∨ χ]] ≃ [φ ∧ ψ] ∨ [φ ∧ χ]. *)
Theorem d37 : forall Σ (φ ψ χ : form Σ),
  equiv (Clos (φ ∧' (ψ ∨' χ)))%dpl ((φ ∧' ψ) ∨' (φ ∧' χ))%dpl.
Proof.
  intros Σ φ ψ χ M g h; split.
  - intros [-> Hn].
    assert (Hs : exists k, sem M (φ ∧' (ψ ∨' χ))%dpl g k).
    { apply NNPP; intro Hno.
      apply Hn; exists g; split; [reflexivity | exact Hno]. }
    destruct Hs as [k [m [Hφ [Ek [j [Hj | Hj]]]]]]; subst k;
      (split; [reflexivity |]).
    + exists j; left; exists m; auto.
    + exists j; right; exists m; auto.
  - intros [-> [k [[m [Hφ Hj]] | [m [Hφ Hj]]]]];
      (split; [reflexivity |]); intros [k' [-> Hn]]; apply Hn.
    + exists m, m; split; [exact Hφ |].
      split; [reflexivity | exists k; left; exact Hj].
    + exists m, m; split; [exact Hφ |].
      split; [reflexivity | exists k; right; exact Hj].
Qed.

(* G&S 1991 §3.4 T 24 / P 64, D38: φ ∨ [♦ψ ∧ χ] ≃ [φ ∨ ψ] ∧ [φ ∨ χ] — the
   closure-restricted distribution law. *)
Theorem d38 : forall Σ (φ ψ χ : form Σ),
  equiv (φ ∨' ((Clos ψ) ∧' χ))%dpl ((φ ∨' ψ) ∧' (φ ∨' χ))%dpl.
Proof.
  intros Σ φ ψ χ M g h; split.
  - intros [-> [k [Hk | [m [[Em Hnn] Hχ]]]]].
    + exists g; split; (split; [reflexivity |]); exists k; left; exact Hk.
    + subst m.
      assert (Hsψ : exists j, sem M ψ g j).
      { apply NNPP; intro Hno.
        apply Hnn; exists g; split; [reflexivity | exact Hno]. }
      destruct Hsψ as [j Hj].
      exists g; split; (split; [reflexivity |]).
      * exists j; right; exact Hj.
      * exists k; right; exact Hχ.
  - intros [k [[Ek Hd1] [Eh Hd2]]]; subst k h.
    split; [reflexivity |].
    destruct Hd1 as [m1 [H1 | H1]].
    + exists m1; left; exact H1.
    + destruct Hd2 as [m2 [H2 | H2]].
      * exists m2; left; exact H2.
      * exists m2; right; exists g; split; [| exact H2].
        split; [reflexivity |].
        intros [j [-> Hn]]; apply Hn; exists m1; exact H1.
Qed.

(* G&S 1991 §3.4 T 24 / P 64, D39: AQV(ψ) ∩ FV(χ) = ∅ ⇒
   φ ∨ [ψ ∧ χ] ≃ [φ ∨ ψ] ∧ [φ ∨ χ] — D38 is the special instance with ♦ψ,
   whose AQV is empty.  Constructive given the transfer machinery. *)
Theorem d39 : forall Σ (φ ψ χ : form Σ),
  disjoint (AQV ψ) (FV χ) ->
  equiv (φ ∨' (ψ ∧' χ))%dpl ((φ ∨' ψ) ∧' (φ ∨' χ))%dpl.
Proof.
  intros Σ φ ψ χ Hdisj M g h; split.
  - intros [-> [k [Hk | [m [Hψ Hχ]]]]].
    + exists g; split; (split; [reflexivity |]); exists k; left; exact Hk.
    + assert (Hag : agree (FV χ) g m)
        by (eapply fact9_agree; [exact Hdisj | exact Hψ]).
      assert (Hχg : true_wrt M χ g)
        by (apply (proj2 (fact8 Σ χ M g m Hag)); exists k; exact Hχ).
      destruct Hχg as [k' Hk'].
      exists g; split; (split; [reflexivity |]).
      * exists m; right; exact Hψ.
      * exists k'; right; exact Hk'.
  - intros [k [[Ek Hd1] [Eh Hd2]]]; subst k h.
    split; [reflexivity |].
    destruct Hd1 as [m1 [H1 | H1]].
    + exists m1; left; exact H1.
    + destruct Hd2 as [m2 [H2 | H2]].
      * exists m2; left; exact H2.
      * assert (Hag : agree (FV χ) g m1)
          by (eapply fact9_agree; [exact Hdisj | exact H1]).
        assert (Hχm : true_wrt M χ m1)
          by (apply (proj1 (fact8 Σ χ M g m1 Hag)); exists m2; exact H2).
        destruct Hχm as [k' Hk'].
        exists k'; right; exists m1; split; [exact H1 | exact Hk'].
Qed.

(* -------------------------------------------------------------------------- *)
(*  Implication (T 24 / P 65)                                                  *)
(* -------------------------------------------------------------------------- *)

(* G&S 1991 §3.4 T 24 / P 65, D40: [¬φ → ψ] ≃ [¬ψ → φ] — contraposition
   with negated antecedents holds unconditionally. *)
Theorem d40 : forall Σ (φ ψ : form Σ),
  equiv ((¬' φ) →' ψ)%dpl ((¬' ψ) →' φ)%dpl.
Proof.
  intros Σ φ ψ M g h; split.
  - intros [-> HC]; split; [reflexivity |].
    intros k [-> Hn].
    apply NNPP; intro Hno.
    destruct (HC g (conj eq_refl Hno)) as [j Hj].
    apply Hn; exists j; exact Hj.
  - intros [-> HC]; split; [reflexivity |].
    intros k [-> Hn].
    apply NNPP; intro Hno.
    destruct (HC g (conj eq_refl Hno)) as [j Hj].
    apply Hn; exists j; exact Hj.
Qed.

(* G&S 1991 §3.4 T 24 / P 65, D41: [♦φ → ψ] ≃ [¬ψ → ¬φ]. *)
Theorem d41 : forall Σ (φ ψ : form Σ),
  equiv ((Clos φ) →' ψ)%dpl ((¬' ψ) →' (¬' φ))%dpl.
Proof.
  intros Σ φ ψ M g h; split.
  - intros [-> HC]; split; [reflexivity |].
    intros k [-> Hnψ].
    exists g; split; [reflexivity |].
    intros [m Hm].
    assert (Hcl : sem M (Clos φ) g g).
    { split; [reflexivity |].
      intros [j [-> Hn]]; apply Hn; exists m; exact Hm. }
    destruct (HC g Hcl) as [j Hj].
    apply Hnψ; exists j; exact Hj.
  - intros [-> HC]; split; [reflexivity |].
    intros k [-> Hnn].
    apply NNPP; intro Hno.
    destruct (HC g (conj eq_refl Hno)) as [j [-> Hnφ]].
    apply Hnn; exists g; split; [reflexivity | exact Hnφ].
Qed.

(* G&S 1991 §3.4 T 24 / P 65, D42: AQV(φ) ∩ FV(ψ) = ∅ ⇒
   [φ → ψ] ≃ [¬ψ → ¬φ] — full contraposition under the no-binding
   condition. *)
Theorem d42 : forall Σ (φ ψ : form Σ),
  disjoint (AQV φ) (FV ψ) ->
  equiv (φ →' ψ)%dpl ((¬' ψ) →' (¬' φ))%dpl.
Proof.
  intros Σ φ ψ Hdisj M g h; split.
  - intros [-> HC]; split; [reflexivity |].
    intros k [-> Hnψ].
    exists g; split; [reflexivity |].
    intros [m Hm].
    destruct (HC m Hm) as [j Hj].
    assert (Hag : agree (FV ψ) g m)
      by (eapply fact9_agree; [exact Hdisj | exact Hm]).
    apply Hnψ.
    apply (proj2 (fact8 Σ ψ M g m Hag)); exists j; exact Hj.
  - intros [-> HC]; split; [reflexivity |].
    intros k Hk.
    assert (Hag : agree (FV ψ) g k)
      by (eapply fact9_agree; [exact Hdisj | exact Hk]).
    apply NNPP; intro Hno.
    assert (Hnψg : ~ exists j, sem M ψ g j).
    { intros [j Hj]; apply Hno.
      apply (proj1 (fact8 Σ ψ M g k Hag)); exists j; exact Hj. }
    destruct (HC g (conj eq_refl Hnψg)) as [m [-> Hnφ]].
    apply Hnφ; exists k; exact Hk.
Qed.

(* G&S 1991 §3.4 T 24 / P 65, D43: [φ → ψ] ≃ ♦[φ → ψ] — an implication is
   a test. *)
Theorem d43 : forall Σ (φ ψ : form Σ),
  equiv (φ →' ψ)%dpl (Clos (φ →' ψ))%dpl.
Proof.
  intros Σ φ ψ M g h; split.
  - intros [-> HC]; split; [reflexivity |].
    intros [k [-> Hn]].
    apply Hn; exists g; split; [reflexivity | exact HC].
  - intros [-> Hnn]; split; [reflexivity |].
    assert (Hs : exists j, sem M (φ →' ψ)%dpl g j).
    { apply NNPP; intro Hno.
      apply Hnn; exists g; split; [reflexivity | exact Hno]. }
    destruct Hs as [j [Ej HC]]; subst j; exact HC.
Qed.

(* G&S 1991 §3.4 T 24 / P 65, D44: [φ → ψ] ≃ [φ → ♦ψ] — an implication
   closes off its consequent. *)
Theorem d44 : forall Σ (φ ψ : form Σ),
  equiv (φ →' ψ)%dpl (φ →' (Clos ψ))%dpl.
Proof.
  intros Σ φ ψ M g h; split.
  - intros [-> HC]; split; [reflexivity |].
    intros k Hk.
    destruct (HC k Hk) as [j Hj].
    exists k; split; [reflexivity |].
    intros [m [-> Hn]]; apply Hn; exists j; exact Hj.
  - intros [-> HC]; split; [reflexivity |].
    intros k Hk.
    destruct (HC k Hk) as [j [-> Hnn]].
    apply NNPP; intro Hno.
    apply Hnn; exists k; split; [reflexivity | exact Hno].
Qed.

(* G&S 1991 §3.4 T 24 / P 65, D45: φ → [ψ → χ] ≃ [φ ∧ ψ] → χ — exportation.
   Constructive. *)
Theorem d45 : forall Σ (φ ψ χ : form Σ),
  equiv (φ →' (ψ →' χ))%dpl ((φ ∧' ψ) →' χ)%dpl.
Proof.
  intros Σ φ ψ χ M g h; split.
  - intros [-> HC]; split; [reflexivity |].
    intros k [m [Hφ Hψ]].
    destruct (HC m Hφ) as [j [-> HC2]].
    exact (HC2 k Hψ).
  - intros [-> HC]; split; [reflexivity |].
    intros k Hφ.
    exists k; split; [reflexivity |].
    intros m Hψ.
    apply HC; exists k; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Quantifiers and connectives (T 24–25 / P 65)                                *)
(* -------------------------------------------------------------------------- *)

(* G&S 1991 §3.4 T 24 / P 65, D46: ∃xφ ∧ ψ ≃ ∃x[φ ∧ ψ] — EGLI'S THEOREM
   (Dekker 2012 §2.1 Observation 1): "the binding power of the existential
   quantifier extends indefinitely to the right".  Constructive,
   axiom-free. *)
Theorem d46_egli : forall Σ (x : Var) (φ ψ : form Σ),
  equiv ((∃' x , φ) ∧' ψ)%dpl (∃' x , (φ ∧' ψ))%dpl.
Proof. intros Σ x φ ψ M; apply rcomp_rex. Qed.

(* G&S 1991 §3.4 T 25 / P 65, D47: x ∉ FV(φ) ∪ AQV(φ) ⇒
   φ ∧ ∃xψ ≃ ∃x[φ ∧ ψ] — leftward scope extension under the usual freeness
   condition plus non-de-activation. *)
Theorem d47 : forall Σ (x : Var) (φ ψ : form Σ),
  ~ In x (FV φ) -> ~ In x (AQV φ) ->
  equiv (φ ∧' (∃' x , ψ))%dpl (∃' x , (φ ∧' ψ))%dpl.
Proof.
  intros Σ x φ ψ HxFV HxAQV M g h; split.
  - intros [k [Hφ [m [Hd Hψ]]]].
    exists (upd g x (m x)); split; [apply dif_upd |].
    exists m; split; [| exact Hψ].
    apply (transfer_given Σ φ M g (upd g x (m x)) k m).
    + intros v Hv.
      assert (Hvx : v <> x) by (intro E; subst v; contradiction).
      symmetry; apply upd_neq; exact Hvx.
    + exact Hφ.
    + intros v Hv.
      assert (Hvx : v <> x) by (intro E; subst v; contradiction).
      apply Hd; exact Hvx.
    + intros v Hv.
      destruct (Nat.eq_dec v x) as [-> | Hvx].
      * symmetry; apply upd_eq.
      * assert (E1 : m v = k v) by (apply Hd; exact Hvx).
        assert (E2 : g v = k v) by (exact (fact9 Σ φ v Hv M g k Hφ)).
        assert (E3 : upd g x (m x) v = g v) by (apply upd_neq; exact Hvx).
        congruence.
  - intros [j [Hd [k' [Hφ Hψ]]]].
    exists (upd k' x (g x)); split.
    + apply (transfer_given Σ φ M j g k' (upd k' x (g x))).
      * intros v Hv.
        assert (Hvx : v <> x) by (intro E; subst v; contradiction).
        apply Hd; exact Hvx.
      * exact Hφ.
      * intros v Hv.
        assert (Hvx : v <> x) by (intro E; subst v; contradiction).
        apply upd_neq; exact Hvx.
      * intros v Hv.
        destruct (Nat.eq_dec v x) as [-> | Hvx].
        -- apply upd_eq.
        -- assert (E1 : upd k' x (g x) v = k' v) by (apply upd_neq; exact Hvx).
           assert (E2 : j v = k' v) by (exact (fact9 Σ φ v Hv M j k' Hφ)).
           assert (E3 : j v = g v) by (apply Hd; exact Hvx).
           congruence.
    + exists k'; split; [| exact Hψ].
      intros y Hy; symmetry; apply upd_neq; exact Hy.
Qed.

(* G&S 1991 §3.4 T 25 / P 65, D48: ∃xφ → ψ ≃ ∀x[φ → ψ] — EGLI'S COROLLARY
   (Dekker 2012 §2.1 Observation 2), "important for the analysis of
   'donkey'-like cases of anaphora": existentials in an antecedent take
   universal force.  Constructive, axiom-free. *)
Theorem d48_egli_corollary : forall Σ (x : Var) (φ ψ : form Σ),
  equiv ((∃' x , φ) →' ψ)%dpl (∀' x , (φ →' ψ))%dpl.
Proof. intros Σ x φ ψ M; apply rimpl_rex. Qed.

(* G&S 1991 §3.4 T 21 / P 62, D14: AQV(φ) ∩ FV(ψ) = ∅ ⇒ φ → ψ ≃ ¬φ ∨ ψ —
   the conditional half of the failed interdefinability D11. *)
Theorem d14 : forall Σ (φ ψ : form Σ),
  disjoint (AQV φ) (FV ψ) ->
  equiv (φ →' ψ)%dpl ((¬' φ) ∨' ψ)%dpl.
Proof.
  intros Σ φ ψ Hdisj M g h; split.
  - intros [-> HC]; split; [reflexivity |].
    destruct (classic (exists k, sem M φ g k)) as [[k Hk] | Hno].
    + destruct (HC k Hk) as [j Hj].
      assert (Hag : agree (FV ψ) g k)
        by (eapply fact9_agree; [exact Hdisj | exact Hk]).
      destruct (proj2 (fact8 Σ ψ M g k Hag)) as [j' Hj'];
        [exists j; exact Hj |].
      exists j'; right; exact Hj'.
    + exists g; left; split; [reflexivity | exact Hno].
  - intros [-> [k [[-> Hn] | Hk]]]; (split; [reflexivity |]); intros m Hm.
    + exfalso; apply Hn; exists m; exact Hm.
    + assert (Hag : agree (FV ψ) g m)
        by (eapply fact9_agree; [exact Hdisj | exact Hm]).
      apply (proj1 (fact8 Σ ψ M g m Hag)); exists k; exact Hk.
Qed.

(* ========================================================================== *)
(*  Part 9 — Countermodels: the non-equivalences of §3.4 (T 20–25 / P 61–66)  *)
(*  All concrete, over the two-element model M_bool (variant M_boolQ),        *)
(*  with input g0 = (λv.false) and output h1 = g0[0 := true].                 *)
(* ========================================================================== *)

(* Any negation-headed (hence any test-shaped) formula misses the properly
   dynamic pair ⟨g0, h1⟩. *)
Lemma neg_fails_g0_h1 : forall φ : form Σ_ex, ~ sem M_bool (¬' φ)%dpl g0 h1.
Proof. intros φ [E _]; exact (h1_neq_g0 E). Qed.

(* ⟨g0, h1⟩ ∈ ⟦∃xPx ∧ Qx⟧ in M_bool. *)
Lemma conj_g0_h1 : sem M_bool ((∃' 0 , Px) ∧' Qx)%dpl g0 h1.
Proof.
  exists h1; split; [exact ex_px_g0_h1 |].
  split; [reflexivity | exact h1_0].
Qed.

(* G&S 1991 §3.4 T 20 / P 61, D4: φ ∧ ψ ≄ ¬[φ → ¬ψ] — the right side is a
   test and "lacks the dynamic binding properties" of the left. *)
Theorem d4 : exists (M : model Σ_ex) (g h : G M),
  sem M ((∃' 0 , Px) ∧' Qx)%dpl g h /\
  ~ sem M (¬' ((∃' 0 , Px) →' (¬' Qx)))%dpl g h.
Proof.
  exists M_bool, g0, h1; split; [exact conj_g0_h1 | apply neg_fails_g0_h1].
Qed.

(* G&S 1991 §3.4 T 20 / P 61, D5: φ ∧ ψ ≄ ¬[¬φ ∨ ¬ψ]. *)
Theorem d5 : exists (M : model Σ_ex) (g h : G M),
  sem M ((∃' 0 , Px) ∧' Qx)%dpl g h /\
  ~ sem M (¬' ((¬' (∃' 0 , Px)) ∨' (¬' Qx)))%dpl g h.
Proof.
  exists M_bool, g0, h1; split; [exact conj_g0_h1 | apply neg_fails_g0_h1].
Qed.

(* G&S 1991 §3.4 T 20 / P 61, D6: ∃xφ ≄ ¬∀x¬φ. *)
Theorem d6 : exists (M : model Σ_ex) (g h : G M),
  sem M (∃' 0 , Px)%dpl g h /\
  ~ sem M (¬' (∀' 0 , (¬' Px)))%dpl g h.
Proof.
  exists M_bool, g0, h1; split; [exact ex_px_g0_h1 | apply neg_fails_g0_h1].
Qed.

(* G&S 1991 §3.4 T 22 / P 62, the D18 instance and HEADLINE COUNTERMODEL:
   ¬¬∃xPx ≄ ∃xPx — double negation destroys binding potential.
   Axiom-free. *)
Theorem negneg_witness : exists (M : model Σ_ex) (g h : G M),
  sem M (∃' 0 , Px)%dpl g h /\
  ~ sem M (¬' ¬' (∃' 0 , Px))%dpl g h.
Proof.
  exists M_bool, g0, h1; split; [exact ex_px_g0_h1 | apply neg_fails_g0_h1].
Qed.

Corollary negneg_not_equiv : ~ equiv (¬' ¬' (∃' 0 , Px))%dpl (∃' 0 , Px)%dpl.
Proof.
  intro He.
  apply (neg_fails_g0_h1 (¬' (∃' 0 , Px))%dpl).
  apply (proj2 (He M_bool g0 h1)); exact ex_px_g0_h1.
Qed.

(* SOURCE NOTE (see Part 8, D34): the printed law "φ ≃ φ ∨ φ" refuted —
   φ ∨ φ is a test, ∃xPx is not. *)
Theorem d34_refuted : exists (M : model Σ_ex) (g h : G M),
  sem M (∃' 0 , Px)%dpl g h /\
  ~ sem M ((∃' 0 , Px) ∨' (∃' 0 , Px))%dpl g h.
Proof.
  exists M_bool, g0, h1; split; [exact ex_px_g0_h1 |].
  intros [E _]; exact (h1_neq_g0 E).
Qed.

Corollary d34_not_equiv :
  ~ equiv (∃' 0 , Px)%dpl ((∃' 0 , Px) ∨' (∃' 0 , Px))%dpl.
Proof.
  intro He.
  destruct (proj1 (He M_bool g0 h1) ex_px_g0_h1) as [E _].
  exact (h1_neq_g0 E).
Qed.

(* G&S 1991 §3.4 T 23 / P 63, D28: φ ∧ ψ ≄ ψ ∧ φ — "the simple example of
   ∃xPx ∧ Qx and Qx ∧ ∃xPx". *)
Theorem d28 : exists (M : model Σ_ex) (g h : G M),
  sem M ((∃' 0 , Px) ∧' Qx)%dpl g h /\
  ~ sem M (Qx ∧' (∃' 0 , Px))%dpl g h.
Proof.
  exists M_bool, g0, h1; split; [exact conj_g0_h1 |].
  intros [k [[-> HQ] _]].
  simpl in HQ; discriminate HQ.
Qed.

(* G&S 1991 §3.4 T 23 / P 63, D29: φ ≄ φ ∧ φ, with the source's own
   counterexample φ := Qx ∧ ∃xPx (interpreting Q as {false}, P as {true}).
   SOURCE NOTE: the typescript misprints this display as "φ ≄ ψ ∧ φ"; the
   journal (P 63) and the prose ("a counterexample against idempotency of
   conjunction as well") fix it. *)
Theorem d29 : exists (M : model Σ_ex) (g h : G M),
  sem M (Qx ∧' (∃' 0 , Px))%dpl g h /\
  ~ sem M ((Qx ∧' (∃' 0 , Px)) ∧' (Qx ∧' (∃' 0 , Px)))%dpl g h.
Proof.
  exists M_boolQ, g0, h1; split.
  - exists g0; split.
    + split; reflexivity.
    + exists h1; split; [apply dif_upd |].
      split; [reflexivity | exact h1_0].
  - intros [k [HL HR]].
    destruct HL as [m [[-> HQ] [k' [Hd [-> HP]]]]].
    destruct HR as [m' [[-> HQ'] _]].
    simpl in HP, HQ'; congruence.
Qed.

(* G&S 1991 §3.4 T 25 / P 66, D49: ∃xφ ≄ ∃y[y/x]φ — renaming a bound
   variable changes the meaning (though not the satisfaction set:
   d49_s_equiv, the source's example after Fact 1, T 16 / P 56). *)
Theorem d49 : exists (M : model Σ_ex) (g h : G M),
  sem M (∃' 0 , Px)%dpl g h /\ ~ sem M (∃' 1 , Py)%dpl g h.
Proof.
  exists M_bool, g0, h1; split; [exact ex_px_g0_h1 |].
  intros [k [Hd [Eh HP]]].
  assert (E : h1 1 = false)
    by (unfold h1; rewrite upd_neq; [reflexivity | discriminate]).
  simpl in HP; congruence.
Qed.

Theorem d49_s_equiv : s_equiv (∃' 0 , Px)%dpl (∃' 1 , Py)%dpl.
Proof.
  intros M g; split.
  - intros [h [k [Hd [-> HP]]]].
    exists (upd g 1 (k 0)), (upd g 1 (k 0)); split; [apply dif_upd |].
    split; [reflexivity |].
    simpl in HP |- *; rewrite upd_eq; exact HP.
  - intros [h [k [Hd [-> HP]]]].
    exists (upd g 0 (k 1)), (upd g 0 (k 1)); split; [apply dif_upd |].
    split; [reflexivity |].
    simpl in HP |- *; rewrite upd_eq; exact HP.
Qed.

(* G&S 1991 §3.4 T 21 / P 62, D11/D12: φ → ψ ≄ ¬φ ∨ ψ, and not even
   ≃s — "an implication is internally dynamic ... disjunction is also
   internally static". *)
Lemma impl_true_g0 : true_wrt M_bool ((∃' 0 , Px) →' Qx)%dpl g0.
Proof.
  exists g0; split; [reflexivity |].
  intros k [k' [Hd [-> HP]]].
  exists k'; split; [reflexivity | exact HP].
Qed.

Lemma disj_not_true_g0 : ~ true_wrt M_bool ((¬' (∃' 0 , Px)) ∨' Qx)%dpl g0.
Proof.
  intros [h [-> [k [[-> Hn] | [-> HQ]]]]].
  - apply Hn; exists h1; exact ex_px_g0_h1.
  - simpl in HQ; discriminate HQ.
Qed.

Theorem d12_not_s_equiv :
  ~ s_equiv ((∃' 0 , Px) →' Qx)%dpl ((¬' (∃' 0 , Px)) ∨' Qx)%dpl.
Proof.
  intro Hs; apply disj_not_true_g0.
  apply (proj1 (Hs M_bool g0)); exact impl_true_g0.
Qed.

Theorem d11_not_equiv :
  ~ equiv ((∃' 0 , Px) →' Qx)%dpl ((¬' (∃' 0 , Px)) ∨' Qx)%dpl.
Proof.
  intro He; exact (d12_not_s_equiv (fact1 _ _ _ He)).
Qed.

(* G&S 1991 §3.4 T 21 / P 62, D8: φ ∧ ψ ≄s ¬[¬φ ∨ ¬ψ] — here even the
   truth conditions differ, "because disjunction is not only externally,
   but also internally static". *)
Theorem d8_not_s_equiv :
  ~ s_equiv ((∃' 0 , Px) ∧' Qx)%dpl (¬' ((¬' (∃' 0 , Px)) ∨' (¬' Qx)))%dpl.
Proof.
  intro Hs.
  destruct (proj1 (Hs M_bool g0)) as [h Hh]; [exists h1; exact conj_g0_h1 |].
  destruct Hh as [-> Hn].
  apply Hn.
  exists g0; split; [reflexivity |].
  exists g0; right.
  split; [reflexivity |].
  intros [j [-> HQ]].
  simpl in HQ; discriminate HQ.
Qed.

Corollary d5_not_equiv :
  ~ equiv ((∃' 0 , Px) ∧' Qx)%dpl (¬' ((¬' (∃' 0 , Px)) ∨' (¬' Qx)))%dpl.
Proof.
  intro He; exact (d8_not_s_equiv (fact1 _ _ _ He)).
Qed.

(* G&S 1991 §3.2, Fact 3 (T 16 / P 56–57): same satisfaction set, same
   production set, different meanings — witnessed by the two tautologies
   Px ∨ ¬Px and ∃x[Px ∨ ¬Px]. *)
Lemma excl_mid_test : forall (M : model Σ_ex) (g : G M),
  sem M (Px ∨' (¬' Px))%dpl g g.
Proof.
  intros M g; split; [reflexivity |].
  destruct (classic (F_pred M Pe (map (tval M g) [TVar 0]))) as [HP | HP].
  - exists g; left; split; [reflexivity | exact HP].
  - exists g; right; split; [reflexivity |].
    intros [j [-> HPj]]; exact (HP HPj).
Qed.

Theorem fact3 :
  s_equiv (Px ∨' (¬' Px))%dpl (∃' 0 , (Px ∨' (¬' Px)))%dpl /\
  p_equiv (Px ∨' (¬' Px))%dpl (∃' 0 , (Px ∨' (¬' Px)))%dpl /\
  ~ equiv (Px ∨' (¬' Px))%dpl (∃' 0 , (Px ∨' (¬' Px)))%dpl.
Proof.
  split; [| split].
  - intros M g; split; intros _.
    + exists g, g; split; [apply dif_refl | apply excl_mid_test].
    + exists g; apply excl_mid_test.
  - intros M h; split; intros _.
    + exists h, h; split; [apply dif_refl | apply excl_mid_test].
    + exists h; apply excl_mid_test.
  - intro He.
    assert (Hrhs : sem M_bool (∃' 0 , (Px ∨' (¬' Px)))%dpl g0 h1).
    { exists h1; split; [apply dif_upd | apply excl_mid_test]. }
    destruct (proj2 (He M_bool g0 h1) Hrhs) as [E _].
    exact (h1_neq_g0 E).
Qed.

(* ========================================================================== *)
(*  Part 10 — Entailment: Facts 10–16 and the separating examples             *)
(*  (§3.5, T 25–29 / P 66–70)                                                 *)
(* ========================================================================== *)

(* G&S 1991 §3.5, Fact 10 (T 26 / P 67): meaning inclusion implies
   s-entailment. *)
Theorem fact10 : forall Σ (φ ψ : form Σ), meaning_incl φ ψ -> s_entails φ ψ.
Proof.
  intros Σ φ ψ H M g [h Hh]; exists h; apply H; exact Hh.
Qed.

(* G&S 1991 §3.5, Fact 11 (Deduction theorem, T 26 / P 67):
   φ ⊨ ψ iff ⊨ φ → ψ.  Constructive. *)
Theorem fact11 : forall Σ (φ ψ : form Σ), entails φ ψ <-> valid (φ →' ψ)%dpl.
Proof.
  intros Σ φ ψ; split.
  - intros H M g.
    exists g; split; [reflexivity |].
    intros k Hk; exact (H M g k Hk).
  - intros H M g h Hgh.
    destruct (H M g) as [j [Ej HC]]; subst j.
    exact (HC h Hgh).
Qed.

(* G&S 1991 §3.5, Fact 12 (T 26 / P 67): φ ⊨s ψ iff ♦φ ⊨ ψ. *)
Theorem fact12 : forall Σ (φ ψ : form Σ),
  s_entails φ ψ <-> entails (Clos φ) ψ.
Proof.
  intros Σ φ ψ; split.
  - intros H M g h [-> Hnn].
    assert (Hs : true_wrt M φ g).
    { apply NNPP; intro Hno.
      apply Hnn; exists g; split; [reflexivity | exact Hno]. }
    exact (H M g Hs).
  - intros H M g [k Hk].
    apply (H M g g).
    split; [reflexivity |].
    intros [m [-> Hn]]; apply Hn; exists k; exact Hk.
Qed.

(* G&S 1991 §3.5, Fact 13 (T 27 / P 68): with no binding relations between
   premiss and conclusion, s-entailment and dynamic entailment coincide. *)
Theorem fact13 : forall Σ (φ ψ : form Σ),
  disjoint (AQV φ) (FV ψ) -> (s_entails φ ψ <-> entails φ ψ).
Proof.
  intros Σ φ ψ Hdisj; split.
  - intros Hs M g h Hgh.
    assert (Hag : agree (FV ψ) g h)
      by (eapply fact9_agree; [exact Hdisj | exact Hgh]).
    apply (proj1 (fact8 Σ ψ M g h Hag)).
    apply (Hs M g); exists h; exact Hgh.
  - intros He M g [h Hh].
    assert (Hag : agree (FV ψ) g h)
      by (eapply fact9_agree; [exact Hdisj | exact Hh]).
    apply (proj2 (fact8 Σ ψ M g h Hag)).
    exact (He M g h Hh).
Qed.

(* G&S 1991 §3.5, Fact 14 (T 27 / P 68): the source's proof verbatim —
   Facts 8 and 9 "play a central role". *)
Theorem fact14 : forall Σ (φ ψ : form Σ),
  disjoint (AQV φ) (FV ψ) -> meaning_incl φ ψ -> entails φ ψ.
Proof.
  intros Σ φ ψ Hdisj Hincl M g h Hgh.
  assert (Hag : agree (FV ψ) g h)
    by (eapply fact9_agree; [exact Hdisj | exact Hgh]).
  apply (proj1 (fact8 Σ ψ M g h Hag)).
  exists h; apply Hincl; exact Hgh.
Qed.

Lemma meaning_incl_refl : forall Σ (φ : form Σ), meaning_incl φ φ.
Proof. intros Σ φ M g h H; exact H. Qed.

(* G&S 1991 §3.5, Fact 15 (Reflexivity, T 27 / P 68): dynamic entailment is
   reflexive on formulas without premiss-internal binding. *)
Theorem fact15 : forall Σ (φ : form Σ),
  disjoint (AQV φ) (FV φ) -> entails φ φ.
Proof.
  intros Σ φ Hdisj; apply fact14; [exact Hdisj | apply meaning_incl_refl].
Qed.

(* G&S 1991 §3.5, unnumbered display after Fact 15 (T 27 / P 68):
   AQV(ψ) ∩ FV(ψ) = ∅ ⇒ φ ∧ ψ ⊨ ψ — restricted weakening. *)
Theorem e_weak : forall Σ (φ ψ : form Σ),
  disjoint (AQV ψ) (FV ψ) -> entails (φ ∧' ψ)%dpl ψ.
Proof.
  intros Σ φ ψ Hdisj M g h [k [H1 H2]].
  assert (Hag : agree (FV ψ) k h)
    by (eapply fact9_agree; [exact Hdisj | exact H2]).
  apply (proj1 (fact8 Σ ψ M k h Hag)).
  exists h; exact H2.
Qed.

(* G&S 1991 §3.5, Def. 21 remarks (T 28 / P 69): x̄-entailment with the empty
   sequence collapses into ⊨, and implies ⊨ in general. *)
Lemma entails_vars_entails : forall Σ xs (φ ψ : form Σ),
  entails_vars xs φ ψ -> entails φ ψ.
Proof.
  intros Σ xs φ ψ H M g h Hgh.
  destruct (H M h) as [k [Hk _]]; [exists g; exact Hgh |].
  exists k; exact Hk.
Qed.

Lemma entails_vars_nil : forall Σ (φ ψ : form Σ),
  entails_vars [] φ ψ <-> entails φ ψ.
Proof.
  intros Σ φ ψ; split.
  - apply entails_vars_entails.
  - intros H M g [g' Hg'].
    destruct (H M g' g Hg') as [k Hk].
    exists k; split; [exact Hk | intros v []].
Qed.

(* G&S 1991 §3.5, Fact 16 (Transitivity, T 29 / P 69): transitivity is
   restored when the middle formula's constraint on the variables it binds
   in the conclusion is carried by the premiss.  SOURCE NOTE: the printed
   proof once swaps AQV(ψ) ∩ FV(χ) to "AQV(χ) ∩ FV(ψ)"; the statement,
   proved here, is the correct one. *)
Theorem fact16 : forall Σ (φ ψ χ : form Σ),
  entails_vars (inter (AQV ψ) (FV χ)) φ ψ -> entails ψ χ -> entails φ χ.
Proof.
  intros Σ φ ψ χ Hev He M g h Hgh.
  destruct (Hev M h) as [k [Hk Hagr]]; [exists g; exact Hgh |].
  assert (Hag : agree (FV χ) k h).
  { intros v Hv.
    destruct (in_dec Nat.eq_dec v (AQV ψ)) as [Hin | Hnin].
    - apply Hagr; apply inter_In; auto.
    - symmetry; exact (fact9 Σ ψ v Hnin M h k Hk). }
  apply (proj1 (fact8 Σ χ M k h Hag)).
  exact (He M h k Hk).
Qed.

(* -------------------------------------------------------------------------- *)
(*  The separating examples of §3.5 (T 26–29 / P 67–69), all concrete          *)
(* -------------------------------------------------------------------------- *)

(* "|=s ∃xPx → Px" (T 26 / P 67): the implication is valid... *)
Theorem valid_ex_impl : valid ((∃' 0 , Px) →' Px)%dpl.
Proof.
  intros M g.
  exists g; split; [reflexivity |].
  intros k [k' [Hd [-> HP]]].
  exists k'; split; [reflexivity | exact HP].
Qed.

(* ... yet ∃xPx ⊭s Px: s-entailment does not account for the binding. *)
Theorem not_s_entails_ex_px : ~ s_entails (∃' 0 , Px)%dpl Px.
Proof.
  intro H.
  destruct (H M_bool g0) as [h [Eh HP]]; [exists h1; exact ex_px_g0_h1 |].
  subst h; simpl in HP; discriminate HP.
Qed.

(* ∃xPx ⊨ Px (T 26 / P 67): dynamic entailment does. *)
Theorem entails_ex_px : entails (∃' 0 , Px)%dpl Px.
Proof.
  intros M g h [k [Hd [-> HP]]].
  exists k; split; [reflexivity | exact HP].
Qed.

(* ∃xPx ⋠ Px (T 26 / P 67): meaning inclusion is "too strict". *)
Theorem not_meaning_incl_ex_px : ~ meaning_incl (∃' 0 , Px)%dpl Px.
Proof.
  intro H.
  destruct (H M_bool g0 h1 ex_px_g0_h1) as [E _].
  exact (h1_neq_g0 E).
Qed.

(* Mutual entailment without equivalence (T 27 / P 68): ∃xPx and Px entail
   each other but differ in meaning. *)
Theorem mutual_entailment_not_equiv :
  entails Px (∃' 0 , Px)%dpl /\ entails (∃' 0 , Px)%dpl Px /\
  ~ equiv (∃' 0 , Px)%dpl Px.
Proof.
  split; [| split].
  - intros M g h [-> HP].
    exists g, g; split; [apply dif_refl |].
    split; [reflexivity | exact HP].
  - exact entails_ex_px.
  - intro He.
    destruct (proj1 (He M_bool g0 h1) ex_px_g0_h1) as [E _].
    exact (h1_neq_g0 E).
Qed.

(* Non-reflexivity (T 27 / P 68): Qx ∧ ∃xQx-style self-binding — the
   source's Px ∧ ∃xQx pattern realised as Qx ∧ ∃xPx in M_boolQ — meaning
   includes itself but does not entail itself. *)
Lemma qx_ex_g0_h1 : sem M_boolQ (Qx ∧' (∃' 0 , Px))%dpl g0 h1.
Proof.
  exists g0; split.
  - split; reflexivity.
  - exists h1; split; [apply dif_upd |].
    split; [reflexivity | exact h1_0].
Qed.

Theorem entails_not_reflexive :
  meaning_incl (Qx ∧' (∃' 0 , Px))%dpl (Qx ∧' (∃' 0 , Px))%dpl /\
  ~ entails (Qx ∧' (∃' 0 , Px))%dpl (Qx ∧' (∃' 0 , Px))%dpl.
Proof.
  split; [apply meaning_incl_refl |].
  intro H.
  destruct (H M_boolQ g0 h1 qx_ex_g0_h1) as [h [m [[-> HQ] _]]].
  simpl in HQ; rewrite h1_0 in HQ; discriminate HQ.
Qed.

(* Non-transitivity (T 27–28 / P 68): ¬¬∃xPx ⊨ ∃xPx and ∃xPx ⊨ Px, but
   ¬¬∃xPx ⊭ Px — the double negation blocks the binding into Px. *)
Theorem entails_not_transitive :
  entails (¬' ¬' (∃' 0 , Px))%dpl (∃' 0 , Px)%dpl /\
  entails (∃' 0 , Px)%dpl Px /\
  ~ entails (¬' ¬' (∃' 0 , Px))%dpl Px.
Proof.
  split; [| split].
  - intros M g h [-> Hnn].
    apply NNPP; intro Hno.
    apply Hnn; exists g; split; [reflexivity | exact Hno].
  - exact entails_ex_px.
  - intro H.
    assert (Hp : sem M_bool (¬' ¬' (∃' 0 , Px))%dpl g0 g0).
    { split; [reflexivity |].
      intros [k [-> Hn]]; apply Hn; exists h1; exact ex_px_g0_h1. }
    destruct (H M_bool g0 g0 Hp) as [h [-> HP]].
    simpl in HP; discriminate HP.
Qed.

(* Order-sensitivity of sequence entailment (Def. 22 remark, T 29 / P 70):
   ∃xPx, ∃xQx ⊨ Qx (the last quantifier binds), but not in the other
   order. *)
Theorem seq_entailment_order_sensitive :
  entails_seq [(∃' 0 , Px)%dpl; (∃' 0 , Qx)%dpl] Qx /\
  ~ entails_seq [(∃' 0 , Qx)%dpl; (∃' 0 , Px)%dpl] Qx.
Proof.
  split.
  - intros M g h [k [H1 [m [H2 Eh]]]]; cbn in Eh; subst h.
    destruct H2 as [m' [Hd [-> HQ]]].
    exists m'; split; [reflexivity | exact HQ].
  - intro H.
    set (k0 := upd g0 0 false).
    set (m0 := upd k0 0 true).
    assert (Hseq : sem_seq M_boolQ [(∃' 0 , Qx)%dpl; (∃' 0 , Px)%dpl] g0 m0).
    { exists k0; split.
      - exists k0; split; [apply dif_upd |].
        split; [reflexivity | apply upd_eq].
      - exists m0; split.
        + exists m0; split; [apply dif_upd |].
          split; [reflexivity | apply upd_eq].
        + reflexivity. }
    destruct (H M_boolQ g0 m0 Hseq) as [h [-> HQ]].
    simpl in HQ; unfold m0 in HQ; rewrite upd_eq in HQ; discriminate HQ.
Qed.

(* Non-monotonicity of sequence entailment (T 29 / P 70): ∃xPx ⊨ Px, yet
   adding the premiss ∃xQx destroys the conclusion. *)
Theorem entails_seq_nonmonotonic :
  entails (∃' 0 , Px)%dpl Px /\
  ~ entails_seq [(∃' 0 , Px)%dpl; (∃' 0 , Qx)%dpl] Px.
Proof.
  split; [exact entails_ex_px |].
  intro H.
  set (k0 := upd g0 0 true).
  set (m0 := upd k0 0 false).
  assert (Hseq : sem_seq M_boolQ [(∃' 0 , Px)%dpl; (∃' 0 , Qx)%dpl] g0 m0).
  { exists k0; split.
    - exists k0; split; [apply dif_upd |].
      split; [reflexivity | apply upd_eq].
    - exists m0; split.
      + exists m0; split; [apply dif_upd |].
        split; [reflexivity | apply upd_eq].
      + reflexivity. }
  destruct (H M_boolQ g0 m0 Hseq) as [h [-> HP]].
  simpl in HP; unfold m0 in HP; rewrite upd_eq in HP; discriminate HP.
Qed.

(* ========================================================================== *)
(*  Part 11 — The donkey sentences (§2.1–2.5, T 2–13 / P 40–53)               *)
(* ========================================================================== *)

Inductive pred_dk : Type := farmer | donkey | own | beat.

Definition Σ_dk : signature :=
  {| Pred := pred_dk;
     arity := fun R => match R with farmer | donkey => 1 | own | beat => 2 end;
     Const := Empty_set |}.

Definition farmer_x : form Σ_dk := @Atom Σ_dk farmer [TVar 0].
Definition donkey_y : form Σ_dk := @Atom Σ_dk donkey [TVar 1].
Definition own_xy   : form Σ_dk := @Atom Σ_dk own    [TVar 0; TVar 1].
Definition beat_xy  : form Σ_dk := @Atom Σ_dk beat   [TVar 0; TVar 1].

(* ∃x[farmer x ∧ ∃y[donkey y ∧ own x y]] — the indefinite antecedent shared
   by (1b), (2b), (3b) (T 2–3 / P 41–42), with x := 0, y := 1. *)
Definition dk_ante : form Σ_dk :=
  (farmer_x ∧' (∃' 1 , (donkey_y ∧' own_xy)))%dpl.

(* "A farmer owns a donkey.  He beats it." — the (1b)-shaped cross-sentential
   conjunction (§2.3, T 2 / P 41): the pronouns are bound from outside the
   syntactic scope of the quantifiers. *)
Definition dk1 : form Σ_dk := ((∃' 0 , dk_ante) ∧' beat_xy)%dpl.

(* "If a farmer owns a donkey, he beats it." — (2b) (§2.4, T 3 / P 42). *)
Definition dk2 : form Σ_dk := ((∃' 0 , dk_ante) →' beat_xy)%dpl.

(* "Every farmer who owns a donkey beats it." — (3b) (§2.5, T 3 / P 42). *)
Definition dk3 : form Σ_dk := (∀' 0 , (dk_ante →' beat_xy))%dpl.

(* [ARTIFACT-iii] sanity checks: the syntactic functions compute. *)
Example aqv_dk1 : AQV dk1 = [0; 1].
Proof. reflexivity. Qed.
Example fv_dk2 : FV dk2 = [].
Proof. reflexivity. Qed.
Example fv_qx_expx : FV (Qx ∧' (∃' 0 , Px))%dpl = [0].
Proof. reflexivity. Qed.

Section Donkey.

Variable Dm : Type.
Variable d0 : Dm.
Variables Fa Dk : Dm -> Prop.
Variables Ow Bt : Dm -> Dm -> Prop.

(* An arbitrary model of the donkey vocabulary. *)
Definition M_dk : model Σ_dk :=
  @Build_model Σ_dk Dm d0 (fun e : Empty_set => match e with end)
    (fun R ds => match R, ds with
                 | farmer, [a]    => Fa a
                 | donkey, [a]    => Dk a
                 | own,    [a; b] => Ow a b
                 | beat,   [a; b] => Bt a b
                 | _, _           => False
                 end).

(* Unpacking the antecedent: an output of ∃x[farmer x ∧ ∃y[donkey y ∧
   own x y]] from g is an assignment k with k[{x,y}]g whose x is a farmer
   owning the donkey at its y. *)
Lemma dk_ante_out : forall (g k : G M_dk),
  sem M_dk (∃' 0 , dk_ante)%dpl g k ->
  (forall v, v <> 0 -> v <> 1 -> k v = g v) /\
  Fa (k 0) /\ Dk (k 1) /\ Ow (k 0) (k 1).
Proof.
  intros g k HEx.
  destruct HEx as [k1 [Hd1 Hante]].
  destruct Hante as [k2 [HFk HEy]].
  destruct HFk as [Ek2 HF].
  destruct HEy as [k3 [Hd3 Hdo]].
  destruct Hdo as [k4 [HDk [Ek HO]]].
  destruct HDk as [Ek4 HD].
  subst k2 k4 k.
  cbn in HF, HD, HO.
  assert (E0 : k3 0 = k1 0) by (apply Hd3; discriminate).
  repeat split.
  - intros v Hv0 Hv1.
    rewrite (Hd3 v Hv1); apply Hd1; exact Hv0.
  - rewrite E0; exact HF.
  - exact HD.
  - exact HO.
Qed.

(* Building an antecedent output: for any farmer/donkey/owning pair ⟨a,b⟩,
   g[x := a][y := b] is an output of the antecedent from g. *)
Lemma dk_ante_in : forall (g : G M_dk) (a b : Dm),
  Fa a -> Dk b -> Ow a b ->
  sem M_dk (∃' 0 , dk_ante)%dpl g (upd (upd g 0 a) 1 b).
Proof.
  intros g a b HFa HDb HOw.
  set (k1 := upd g 0 a).
  set (k3 := upd k1 1 b).
  exists k1; split; [apply dif_upd |].
  exists k1; split.
  - split; [reflexivity | exact HFa].
  - exists k3; split; [apply dif_upd |].
    exists k3; split.
    + split; [reflexivity | exact HDb].
    + split; [reflexivity | exact HOw].
Qed.

(* DK1, relational meaning (§2.3, T 7 / P 46 computation style): ⟦dk1⟧ is
   the set of pairs ⟨g,h⟩ with h[{x,y}]g, h(x) a farmer, h(y) a donkey he
   owns and beats.  The ⇐ direction identifies the prescribed output with
   an update chain, hence extensionality [ARTIFACT-iv(a)]. *)
Theorem dk1_meaning : forall (g h : G M_dk),
  sem M_dk dk1 g h <->
  ((forall v, v <> 0 -> v <> 1 -> h v = g v) /\
   Fa (h 0) /\ Dk (h 1) /\ Ow (h 0) (h 1) /\ Bt (h 0) (h 1)).
Proof.
  intros g h; split.
  - intros [k [HEx [Eh HB]]]; subst h.
    cbn in HB.
    destruct (dk_ante_out g k HEx) as [Hout [HF [HD HO]]].
    repeat split; assumption.
  - intros [Hout [HF [HD [HO HB]]]].
    assert (E : upd (upd g 0 (h 0)) 1 (h 1) = h).
    { apply assign_ext; intro v.
      destruct (Nat.eq_dec v 1) as [-> | Hv1]; [apply upd_eq |].
      rewrite upd_neq; [| exact Hv1].
      destruct (Nat.eq_dec v 0) as [-> | Hv0]; [apply upd_eq |].
      rewrite upd_neq; [| exact Hv0].
      symmetry; apply Hout; assumption. }
    exists h; split.
    + rewrite <- E; apply dk_ante_in; assumption.
    + split; [reflexivity |]; cbn; exact HB.
Qed.

(* DK1, truth conditions (§2.3, T 7 / P 46): "A farmer owns a donkey.  He
   beats it." is true with respect to g iff some farmer owns and beats some
   donkey — the classical (1a)-style content ∃x∃y[...], recovered without
   extensionality (the witness update chain is used as the same term at
   every test step). *)
Theorem dk1_truth : forall g : G M_dk,
  true_wrt M_dk dk1 g <-> exists a b, Fa a /\ Dk b /\ Ow a b /\ Bt a b.
Proof.
  intros g; split.
  - intros [h [k [HEx [Eh HB]]]]; subst h.
    cbn in HB.
    destruct (dk_ante_out g k HEx) as [Hout [HF [HD HO]]].
    exists (k 0), (k 1); repeat split; assumption.
  - intros [a [b [HFa [HDb [HOw HBt]]]]].
    set (k3 := upd (upd g 0 a) 1 b).
    exists k3, k3; split.
    + apply dk_ante_in; assumption.
    + split; [reflexivity | exact HBt].
Qed.

(* DK2, relational meaning (§2.4, T 9–10 / P 48–49): the conditional donkey
   sentence is a test — true iff every farmer beats every donkey he owns.
   Constructive, axiom-free. *)
Theorem dk2_meaning : forall (g h : G M_dk),
  sem M_dk dk2 g h <->
  (h = g /\ forall a b, Fa a -> Dk b -> Ow a b -> Bt a b).
Proof.
  intros g h; split.
  - intros [-> HC]; split; [reflexivity |].
    intros a b HFa HDb HOw.
    destruct (HC (upd (upd g 0 a) 1 b) (dk_ante_in g a b HFa HDb HOw))
      as [j [-> HB]].
    exact HB.
  - intros [-> Hall]; split; [reflexivity |].
    intros k HEx.
    destruct (dk_ante_out g k HEx) as [Hout [HF [HD HO]]].
    exists k; split; [reflexivity |]; cbn.
    exact (Hall (k 0) (k 1) HF HD HO).
Qed.

(* DK2, truth conditions: exactly the (2a)-content
   ∀x∀y[[farmer x ∧ donkey y ∧ own x y] → beat x y] (T 3 / P 41–42).
   Constructive, axiom-free. *)
Theorem dk2_truth : forall g : G M_dk,
  true_wrt M_dk dk2 g <-> (forall a b, Fa a -> Dk b -> Ow a b -> Bt a b).
Proof.
  intros g; split.
  - intros [h Hh].
    destruct (proj1 (dk2_meaning g h) Hh) as [_ Hall]; exact Hall.
  - intros Hall.
    exists g; apply (proj2 (dk2_meaning g g)); split; [reflexivity | exact Hall].
Qed.

(* DK3: (2b) and (3b) are equivalent — an instance of Egli's Corollary D48,
   which the source calls "important for the analysis of 'donkey'-like
   cases" (T 25 / P 65; computation of (3b) in §2.5, T 11–12 / P 50–51).
   Constructive, axiom-free. *)
Theorem dk2_dk3_equiv : equiv dk2 dk3.
Proof. exact (d48_egli_corollary Σ_dk 0 dk_ante beat_xy). Qed.

(* DK3, truth conditions, by transport along the equivalence. *)
Theorem dk3_truth : forall g : G M_dk,
  true_wrt M_dk dk3 g <-> (forall a b, Fa a -> Dk b -> Ow a b -> Bt a b).
Proof.
  intros g; split.
  - intro Ht.
    apply (proj1 (dk2_truth g)).
    apply (proj2 (fact1 _ _ _ dk2_dk3_equiv M_dk g)); exact Ht.
  - intro Hall.
    apply (proj1 (fact1 _ _ _ dk2_dk3_equiv M_dk g)).
    apply (proj2 (dk2_truth g)); exact Hall.
Qed.

End Donkey.

(* ========================================================================== *)
(*  Part 12 — Assumption audit                                                 *)
(* ========================================================================== *)
(* Output of the commands below under Coq 8.20.1 (2026-09-05):
     Group 1 (18 theorems): "Closed under the global context" — the
       headline results (Fact 9, the transfer lemma, Fact 8, Egli's
       Theorem D46 and Corollary D48, associativity D27, the ¬¬ and
       ∨-idempotency countermodels, D28, D29, D49, the deduction theorem,
       transitivity Fact 16, and both donkey truth conditions with the
       dk2 ≃ dk3 equivalence) use no axioms at all.
     Group 2: exactly [classic] — the laws whose set-theoretic proofs in
       the source are classical.
     Group 3: exactly [functional_extensionality_dep] (and NOT classic) —
       precisely the results that must produce a prescribed output
       assignment (the given-output transfer lemma and its clients D32,
       D33, D47, the Fact 6 refutation, and the dk1 relational meaning).
   No other axiom, Parameter or Hypothesis occurs anywhere in the file.  *)

(* Group 1 — expected: "Closed under the global context" (axiom-free). *)
Print Assumptions fact9.
Print Assumptions transfer.
Print Assumptions fact8.
Print Assumptions d16.
Print Assumptions d27_conj_assoc.
Print Assumptions d46_egli.
Print Assumptions d48_egli_corollary.
Print Assumptions negneg_witness.
Print Assumptions d34_refuted.
Print Assumptions d28.
Print Assumptions d29.
Print Assumptions d49.
Print Assumptions fact11.
Print Assumptions fact16.
Print Assumptions dk1_truth.
Print Assumptions dk2_truth.
Print Assumptions dk2_dk3_equiv.
Print Assumptions dk3_truth.

(* Group 2 — expected: Classical.classic only. *)
Print Assumptions d1.
Print Assumptions d2.
Print Assumptions d3.
Print Assumptions d18.
Print Assumptions d20.
Print Assumptions d14.
Print Assumptions d42.
Print Assumptions fact3.
Print Assumptions fact12.

(* Group 3 — expected: functional_extensionality_dep (some also classic). *)
Print Assumptions transfer_given.
Print Assumptions d32.
Print Assumptions d33.
Print Assumptions d47.
Print Assumptions fact6_refuted.
Print Assumptions dk1_meaning.

(* ========================================================================== *)
(*  End of DPL.v                                                               *)
(* ========================================================================== *)
