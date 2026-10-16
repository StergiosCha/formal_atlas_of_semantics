(* Gallin (1975), p. 60: A1, A2, A3, AS4 and the one-occurrence rule R.
   A1-A3 use variables as in the source, not arbitrary semantic assertions.
   This is a theorem calculus: there is no rule admitting a local hypothesis
   as an unconditional theorem. Model truth is absent from Derivation. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Models.
From MontagueGallin Require Import Types Target Minimal Independent Substitution.
Import ListNotations.
Set Implicit Arguments.

Definition axiom1 {S P G} (g : ctm S P G (garr gt gt)) : ctm S P G gt :=
  CEq (cand (CApp g ctrue) (CApp g cfalse)) (call (CApp (cweaken g) (CVar gz))).
Definition axiom2 {S P G a} (x y : ctm S P G a) (f : ctm S P G (garr a gt)) :=
  cimp (CEq x y) (CEq (CApp f x) (CApp f y)).
Definition axiom3 {S P G a b} (f g : ctm S P G (garr a b)) : ctm S P G gt :=
  CEq (call (CEq (CApp (cweaken f) (CVar gz)) (CApp (cweaken g) (CVar gz)))) (CEq f g).
Definition axiom4 {S P G a b} (p : ctm S P (a :: G) b) (q : ctm S P G a) :=
  CEq (CApp (CLam p) q) (subst0 p q).

Section AxiomSemantics.
Context {S P : gty -> Type} {E I : Type}.
Variable B : BooleanTruth.
Variable FE : FunExt.
Variable lex : forall a, S a -> value_domain E I a.
Variable theta : forall a, P a -> value_domain E I a.
Local Notation V := (ceval B lex theta).

Lemma boolean_exhaustiveness (f : bool -> bool) :
  andb (f true) (f false) = truth B (forall x, f x = true).
Proof.
  symmetry; apply truth_from_spec; rewrite Bool.andb_true_iff.
  split; [intros [HT HF] []; assumption | intro H; split; apply H].
Qed.
Theorem axiom1_valid G (g : ctm S P G (garr gt gt)) rho : V (axiom1 g) rho = true.
Proof.
  change (truth B (V (cand (CApp g ctrue) (CApp g cfalse)) rho =
    V (call (CApp (cweaken g) (CVar gz))) rho) = true).
  apply (proj2 (truth_spec B _)).
  rewrite ceval_and, ceval_all by exact FE.
  assert (HT : V (CApp g ctrue) rho = V g rho true).
  { change (V g rho (V ctrue rho) = V g rho true); rewrite ceval_true; reflexivity. }
  assert (HF : V (CApp g cfalse) rho = V g rho false).
  { change (V g rho (V cfalse rho) = V g rho false); rewrite ceval_false; reflexivity. }
  assert (HX : forall x, V (CApp (cweaken g) (CVar gz)) (@value_extend E I G gt rho x) = V g rho x).
  { intro x; change (V (cweaken g) (@value_extend E I G gt rho x) x = V g rho x).
    rewrite ceval_weaken by exact FE; reflexivity. }
  rewrite HT, HF, boolean_exhaustiveness; apply truth_congr; split; intros H x.
  - rewrite HX; apply H.
  - specialize (H x); rewrite HX in H; exact H.
Qed.
Theorem axiom2_valid G a (x y : ctm S P G a) (f : ctm S P G (garr a gt)) rho :
  V (axiom2 x y f) rho = true.
Proof.
  unfold axiom2; rewrite ceval_imp by exact FE; cbn [ceval].
  destruct (truth B (V x rho = V y rho)) eqn:H; cbn; auto.
  apply (proj1 (truth_spec B _)) in H; rewrite H.
  apply (proj2 (truth_spec B _)); reflexivity.
Qed.
Theorem axiom3_valid G a b (f g : ctm S P G (garr a b)) rho : V (axiom3 f g) rho = true.
Proof.
  change (truth B (V (call (CEq (CApp (cweaken f) (CVar gz))
    (CApp (cweaken g) (CVar gz)))) rho = truth B (V f rho = V g rho)) = true).
  apply (proj2 (truth_spec B _)); rewrite ceval_all by exact FE.
  assert (K : forall x, V (CEq (CApp (cweaken f) (CVar gz)) (CApp (cweaken g) (CVar gz)))
    (@value_extend E I G a rho x) = truth B (V f rho x = V g rho x)).
  { intro x; change (truth B (V (cweaken f) (@value_extend E I G a rho x) x =
      V (cweaken g) (@value_extend E I G a rho x) x) = truth B (V f rho x = V g rho x)).
    rewrite !ceval_weaken by exact FE; reflexivity. }
  apply truth_congr; split.
  - intro H; apply FE; intro x; specialize (H x); rewrite K in H.
    apply (proj1 (truth_spec B _)); exact H.
  - intros H x; rewrite K; apply (proj2 (truth_spec B _)); rewrite H; reflexivity.
Qed.
Theorem axiom4_valid G a b (p : ctm S P (a :: G) b) (q : ctm S P G a) rho :
  V (axiom4 p q) rho = true.
Proof. apply (proj2 (truth_spec B _)); apply beta_interpretation; exact FE. Qed.
End AxiomSemantics.

Section ProofTheory.
Context (S P : gty -> Type).
(* Both variable representations count as source variables. Constants and
   compound terms do not become A1-A3 instances merely by being well typed. *)
Inductive axiom_variable (G : list gty) (a : gty) : Type :=
| ContextVariable : gvar G a -> axiom_variable G a
| ParameterVariable : P a -> axiom_variable G a.
Definition variable_term G a (v : axiom_variable G a) : ctm S P G a :=
  match v with @ContextVariable _ _ w => CVar w | @ParameterVariable _ _ n => CFree n end.
Inductive Ty2Axiom : forall G, ctm S P G gt -> Type :=
| A1 : forall G (g : axiom_variable G (garr gt gt)), Ty2Axiom (axiom1 (variable_term g))
| A2 : forall G a (x y : axiom_variable G a) (f : axiom_variable G (garr a gt)),
    Ty2Axiom (axiom2 (variable_term x) (variable_term y) (variable_term f))
| A3 : forall G a b (f g : axiom_variable G (garr a b)), Ty2Axiom (axiom3 (variable_term f) (variable_term g))
| AS4 : forall G a b (p : ctm S P (a :: G) b) (q : ctm S P G a), Ty2Axiom (axiom4 p q).
Inductive Derivation : forall G, ctm S P G gt -> Type :=
| ByAxiom : forall G (p : ctm S P G gt), Ty2Axiom p -> Derivation p
| ByReplacement : forall D a G (p q : ctm S P D a) (C : ccontext S P D a G gt),
    Derivation (CEq p q) -> Derivation (plug C p) -> Derivation (plug C q).
End ProofTheory.
Arguments ContextVariable {P G a} _.
Arguments ParameterVariable {P G a} _.
Arguments variable_term {S P G a} _.
Arguments A1 {S P G} g.
Arguments A2 {S P G a} x y f.
Arguments A3 {S P G a b} f g.
Arguments AS4 {S P G a b} p q.
Arguments ByAxiom {S P G p} _.
Arguments ByReplacement {S P D a G p q} C _ _.

Theorem ty2_axioms_sound {S P E I} (B : BooleanTruth) (FE : FunExt)
  (lex : forall a, S a -> value_domain E I a) (theta : forall a, P a -> value_domain E I a)
  G (p : ctm S P G gt) (H : Ty2Axiom p) rho : ceval B lex theta p rho = true.
Proof.
  destruct H; [apply axiom1_valid | apply axiom2_valid | apply axiom3_valid | apply axiom4_valid]; exact FE.
Qed.
Theorem ty2_derivations_sound {S P E I} (B : BooleanTruth) (FE : FunExt)
  (lex : forall a, S a -> value_domain E I a) (theta : forall a, P a -> value_domain E I a)
  G (p : ctm S P G gt) (H : Derivation p) : forall rho, ceval B lex theta p rho = true.
Proof.
  induction H as [G p HA | D a G p q C HE IHE HB IHB]; intro rho.
  - apply ty2_axioms_sound; [exact FE | exact HA].
  - rewrite <- (@replacement_preserves_global_equality S P E I B FE lex theta D a G gt C p q).
    + apply IHB.
    + intro tau; apply (proj1 (truth_spec B _)); apply IHE.
Qed.

Corollary standard_model_derivation_soundness {S P} (N : standard_model S) theta
  G (p : ctm S P G gt) (H : Derivation p) rho :
  ceval (standard_truth N) (standard_lex N) theta p rho = true.
Proof. apply ty2_derivations_sound; [exact (standard_extensionality N) | exact H]. Qed.

(* These are actual derivation trees, using AS4 and R, not constructions
   that insert a host-level equality as an object-language proof. *)
Definition derive_reflexivity {S P G a} (p : ctm S P G a) : Derivation (CEq p p) :=
  ByReplacement (EqLeft Hole p)
    (ByAxiom (AS4 (CVar gz) p)) (ByAxiom (AS4 (CVar gz) p)).
Definition derive_symmetry {S P G a} (p q : ctm S P G a)
  (H : Derivation (CEq p q)) : Derivation (CEq q p) :=
  ByReplacement (EqLeft Hole p) H (derive_reflexivity p).
Definition derive_transitivity {S P G a} (p q r : ctm S P G a)
  (H1 : Derivation (CEq p q)) (H2 : Derivation (CEq q r)) : Derivation (CEq p r) :=
  ByReplacement (EqRight p Hole) H2 H1.
Definition derive_context_congruence {S P D a G b} (C : ccontext S P D a G b)
  (p q : ctm S P D a) (H : Derivation (CEq p q)) :
  Derivation (CEq (plug C p) (plug C q)) :=
  ByReplacement (EqRight (plug C p) C) H (derive_reflexivity (plug C p)).
Definition derive_truth {S P G} : Derivation (@ctrue S P G) :=
  derive_reflexivity (@CLam S P G gt gt (CVar gz)).
Definition derive_beta_expansion {S P G a} (p : ctm S P (a :: G) gt) (q : ctm S P G a)
  (H : Derivation (subst0 p q)) : Derivation (CApp (CLam p) q) :=
  ByReplacement Hole (derive_symmetry (ByAxiom (AS4 p q))) H.
