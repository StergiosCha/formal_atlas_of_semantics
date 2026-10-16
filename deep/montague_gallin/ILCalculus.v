(* Gallin (1975), pp. 19-20. The alternative AS4.1-AS4.7 and R1-R8
   are given explicitly in the source. This implements that presentation,
   not an unchecked unrestricted substitution principle. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Minimal Untensed Calculus ILCore.
Import ListNotations.
Set Implicit Arguments.

Inductive il_axiom_variable (G : list ty) (a : ty) : Type :=
| ILContextVariable : var G a -> il_axiom_variable G a
| ILNamedVariable : nat -> il_axiom_variable G a.
Arguments ILContextVariable {G a} _.
Arguments ILNamedVariable {G a} _.
Definition il_variable_term G a (v : il_axiom_variable G a) : ltm G a :=
  match v with ILContextVariable w => LVar w | ILNamedVariable n => LFree n end.
Arguments il_variable_term {G a} _.
Lemma il_variable_is_modally_closed G a (v : il_axiom_variable G a) :
  ModallyClosed (il_variable_term v).
Proof. destruct v; constructor. Qed.

Definition il_axiom1 {G} (g : ltm G (arr t t)) :=
  LEq (land (LApp g ltrue) (LApp g lfalse)) (lall (LApp (lweaken g) (LVar vz))).
Definition il_axiom2 {G a} (x y : ltm G a) (f : ltm G (arr a t)) :=
  limp (LEq x y) (LEq (LApp f x) (LApp f y)).
Definition il_axiom3 {G a b} (f g : ltm G (arr a b)) :=
  LEq (lall (LEq (LApp (lweaken f) (LVar vz)) (LApp (lweaken g) (LVar vz)))) (LEq f g).
Definition il_axiom5 {G a} (f g : ltm G (intens a)) :=
  LEq (lbox (LEq (LDown f) (LDown g))) (LEq f g).

Inductive ILAxiom : forall G, ltm G t -> Type :=
| IL_A1 : forall G (g : il_axiom_variable G (arr t t)), ILAxiom (il_axiom1 (il_variable_term g))
| IL_A2 : forall G a (x y : il_axiom_variable G a) (f : il_axiom_variable G (arr a t)),
    ILAxiom (il_axiom2 (il_variable_term x) (il_variable_term y) (il_variable_term f))
| IL_A3 : forall G a b (f g : il_axiom_variable G (arr a b)),
    ILAxiom (il_axiom3 (il_variable_term f) (il_variable_term g))
| IL_AS41 : forall G a b (p : ltm G b) (q : ltm G a),
    ILAxiom (LEq (LApp (LLam (lweaken p)) q) p)
| IL_AS42 : forall G a (q : ltm G a), ILAxiom (LEq (LApp (LLam (LVar vz)) q) q)
| IL_AS43 : forall G a b c (p : ltm (a :: G) (arr b c)) (r : ltm (a :: G) b) (q : ltm G a),
    ILAxiom (LEq (LApp (LLam (LApp p r)) q) (LApp (LApp (LLam p) q) (LApp (LLam r) q)))
| IL_AS44 : forall G a b (p r : ltm (a :: G) b) (q : ltm G a),
    ILAxiom (LEq (LApp (LLam (LEq p r)) q) (LEq (LApp (LLam p) q) (LApp (LLam r) q)))
| IL_AS45 : forall G a b c (p : ltm (b :: a :: G) c) (q : ltm G a),
    ILAxiom (LEq (LApp (LLam (LLam p)) q)
      (LLam (LApp (LLam (lrename p lswap)) (lweaken q))))
| IL_AS46 : forall G a b (p : ltm (a :: G) (intens b)) (q : ltm G a),
    ILAxiom (LEq (LApp (LLam (LDown p)) q) (LDown (LApp (LLam p) q)))
| IL_AS47 : forall G a b (p : ltm (a :: G) b) (q : ltm G a), ModallyClosed q ->
    ILAxiom (LEq (LApp (LLam (LUp p)) q) (LUp (LApp (LLam p) q)))
| IL_A5 : forall G a (f g : il_axiom_variable G (intens a)),
    ILAxiom (il_axiom5 (il_variable_term f) (il_variable_term g))
| IL_AS6 : forall G a (p : ltm G a), ILAxiom (LEq (LDown (LUp p)) p).

Inductive ILDerivation : forall G, ltm G t -> Type :=
| ILByAxiom : forall G (p : ltm G t), ILAxiom p -> ILDerivation p
| IL_R1 : forall G (p q : ltm G t), ILDerivation (LEq p q) -> ILDerivation p -> ILDerivation q
| IL_R2 : forall G a b (p q : ltm G (arr a b)) (r : ltm G a),
    ILDerivation (LEq p q) -> ILDerivation (LEq (LApp p r) (LApp q r))
| IL_R3 : forall G a b (p q : ltm G a) (r : ltm G (arr a b)),
    ILDerivation (LEq p q) -> ILDerivation (LEq (LApp r p) (LApp r q))
| IL_R4 : forall G a b (p q : ltm (a :: G) b),
    ILDerivation (LEq p q) -> ILDerivation (LEq (LLam p) (LLam q))
| IL_R5 : forall G a (p q : ltm G a),
    ILDerivation (LEq p q) -> ILDerivation (LEq (LUp p) (LUp q))
| IL_R6 : forall G a (p q : ltm G (intens a)),
    ILDerivation (LEq p q) -> ILDerivation (LEq (LDown p) (LDown q))
| IL_R7 : forall G a (p q r : ltm G a),
    ILDerivation (LEq p q) -> ILDerivation (LEq (LEq r p) (LEq r q))
| IL_R8 : forall G a (p q r : ltm G a),
    ILDerivation (LEq p q) -> ILDerivation (LEq (LEq p r) (LEq q r)).
Arguments ILByAxiom {G p} _.
Arguments IL_R1 {G p q} _ _.
Arguments IL_R2 {G a b p q} r _.
Arguments IL_R3 {G a b p q} r _.
Arguments IL_R4 {G a b p q} _.
Arguments IL_R5 {G a p q} _.
Arguments IL_R6 {G a p q} _.
Arguments IL_R7 {G a p q} r _.
Arguments IL_R8 {G a p q} r _.

Section Soundness.
Variable M : il_model.
Variable sigma : il_free_env M.
Local Notation B := (il_truth M).
Local Notation FE := (il_extensionality M).

Lemma lval_eq_true G a (p q : ltm G a) rho i :
  lval M (LEq p q) rho sigma i = true <-> lval M p rho sigma i = lval M q rho sigma i.
Proof. apply truth_spec. Qed.
Theorem il_axiom1_valid G (g : ltm G (arr t t)) rho i : lval M (il_axiom1 g) rho sigma i = true.
Proof.
  apply lval_eq_true; rewrite lval_and, lval_all.
  assert (HT : lval M (LApp g ltrue) rho sigma i = lval M g rho sigma i true).
  { change (lval M g rho sigma i (lval M ltrue rho sigma i) = lval M g rho sigma i true).
    rewrite lval_true; reflexivity. }
  assert (HF : lval M (LApp g lfalse) rho sigma i = lval M g rho sigma i false).
  { change (lval M g rho sigma i (lval M lfalse rho sigma i) = lval M g rho sigma i false).
    rewrite lval_false; reflexivity. }
  assert (HX : forall x, lval M (LApp (lweaken g) (LVar vz)) (@il_extend M G t rho x) sigma i =
    lval M g rho sigma i x).
  { intro x; change (lval M (lweaken g) (@il_extend M G t rho x) sigma i x = lval M g rho sigma i x).
    rewrite lval_weaken; reflexivity. }
  rewrite HT, HF, (boolean_exhaustiveness B); apply truth_congr; split; intros H x.
  - rewrite HX; apply H.
  - specialize (H x); rewrite HX in H; exact H.
Qed.
Theorem il_axiom2_valid G a (x y : ltm G a) (f : ltm G (arr a t)) rho i :
  lval M (il_axiom2 x y f) rho sigma i = true.
Proof.
  unfold il_axiom2; rewrite lval_imp.
  change (orb (negb (truth B (lval M x rho sigma i = lval M y rho sigma i)))
    (truth B (lval M f rho sigma i (lval M x rho sigma i) =
      lval M f rho sigma i (lval M y rho sigma i))) = true).
  destruct (truth B (lval M x rho sigma i = lval M y rho sigma i)) eqn:H; cbn; auto.
  apply (proj1 (truth_spec B _)) in H; rewrite H; apply (proj2 (truth_spec B _)); reflexivity.
Qed.
Theorem il_axiom3_valid G a b (f g : ltm G (arr a b)) rho i :
  lval M (il_axiom3 f g) rho sigma i = true.
Proof.
  apply lval_eq_true; rewrite lval_all.
  change (truth B (forall x, lval M (LEq (LApp (lweaken f) (LVar vz))
    (LApp (lweaken g) (LVar vz))) (@il_extend M G a rho x) sigma i = true) =
    truth B (lval M f rho sigma i = lval M g rho sigma i)).
  apply truth_congr; split.
  - intro H; apply FE; intro x; specialize (H x); apply lval_eq_true in H.
    change (lval M (lweaken f) (@il_extend M G a rho x) sigma i x =
      lval M (lweaken g) (@il_extend M G a rho x) sigma i x) in H.
    rewrite !lval_weaken in H; exact H.
  - intros H x; apply lval_eq_true.
    change (lval M (lweaken f) (@il_extend M G a rho x) sigma i x =
      lval M (lweaken g) (@il_extend M G a rho x) sigma i x).
    rewrite !lval_weaken, H; reflexivity.
Qed.
Theorem il_axiom5_valid G a (f g : ltm G (intens a))
  (HF : ModallyClosed f) (HG : ModallyClosed g) rho i :
  lval M (il_axiom5 f g) rho sigma i = true.
Proof.
  apply lval_eq_true; rewrite lval_box.
  change (truth B (forall j, lval M (LEq (LDown f) (LDown g)) rho sigma j = true) =
    truth B (lval M f rho sigma i = lval M g rho sigma i)).
  apply truth_congr; split.
  - intro H; apply FE; intro j; specialize (H j); apply lval_eq_true in H.
    change (lval M f rho sigma j j = lval M g rho sigma j j) in H.
    rewrite (modally_closed_is_index_independent sigma HF rho j i),
      (modally_closed_is_index_independent sigma HG rho j i) in H; exact H.
  - intros H j; apply lval_eq_true.
    change (lval M f rho sigma j j = lval M g rho sigma j j).
    rewrite (modally_closed_is_index_independent sigma HF rho j i),
      (modally_closed_is_index_independent sigma HG rho j i), H; reflexivity.
Qed.

Theorem il_axioms_sound G (p : ltm G t) (H : ILAxiom p) rho i : lval M p rho sigma i = true.
Proof.
  destruct H.
  - apply il_axiom1_valid.
  - apply il_axiom2_valid.
  - apply il_axiom3_valid.
  - apply lval_eq_true; apply lval_weaken.
  - apply lval_eq_true; reflexivity.
  - apply lval_eq_true; reflexivity.
  - apply lval_eq_true; reflexivity.
  - apply lval_eq_true.
    change ((fun y => lval M p (il_extend (il_extend rho (lval M q rho sigma i)) y) sigma i) =
      (fun y => lval M (lrename p lswap)
        (il_extend (il_extend rho y) (lval M (lweaken q) (il_extend rho y) sigma i)) sigma i)).
    apply FE; intro y; rewrite lval_weaken, lval_swap; reflexivity.
  - apply lval_eq_true; reflexivity.
  - apply lval_eq_true.
    change ((fun j => lval M p (il_extend rho (lval M q rho sigma i)) sigma j) =
      (fun j => lval M p (il_extend rho (lval M q rho sigma j)) sigma j)).
    apply FE; intro j; rewrite (modally_closed_is_index_independent sigma m rho i j); reflexivity.
  - apply il_axiom5_valid; apply il_variable_is_modally_closed.
  - apply lval_eq_true; reflexivity.
Qed.

Theorem il_derivations_sound G (p : ltm G t) (H : ILDerivation p) :
  forall rho i, lval M p rho sigma i = true.
Proof.
  induction H; intros rho idx.
  - apply il_axioms_sound; assumption.
  - specialize (IHILDerivation1 rho idx); apply lval_eq_true in IHILDerivation1.
    rewrite <- IHILDerivation1; apply IHILDerivation2.
  - apply lval_eq_true; specialize (IHILDerivation rho idx); apply lval_eq_true in IHILDerivation.
    change (lval M p rho sigma idx (lval M r rho sigma idx) = lval M q rho sigma idx (lval M r rho sigma idx)).
    rewrite IHILDerivation; reflexivity.
  - apply lval_eq_true; specialize (IHILDerivation rho idx); apply lval_eq_true in IHILDerivation.
    change (lval M r rho sigma idx (lval M p rho sigma idx) = lval M r rho sigma idx (lval M q rho sigma idx)).
    rewrite IHILDerivation; reflexivity.
  - apply lval_eq_true.
    change ((fun x => lval M p (il_extend rho x) sigma idx) =
      (fun x => lval M q (il_extend rho x) sigma idx)).
    apply FE; intro x; apply lval_eq_true; apply IHILDerivation.
  - apply lval_eq_true.
    change ((fun j => lval M p rho sigma j) = (fun j => lval M q rho sigma j)).
    apply FE; intro j; apply lval_eq_true; apply IHILDerivation.
  - apply lval_eq_true; specialize (IHILDerivation rho idx); apply lval_eq_true in IHILDerivation.
    change (lval M p rho sigma idx idx = lval M q rho sigma idx idx); rewrite IHILDerivation; reflexivity.
  - apply lval_eq_true; specialize (IHILDerivation rho idx); apply lval_eq_true in IHILDerivation.
    change (truth B (lval M r rho sigma idx = lval M p rho sigma idx) =
      truth B (lval M r rho sigma idx = lval M q rho sigma idx)); rewrite IHILDerivation; reflexivity.
  - apply lval_eq_true; specialize (IHILDerivation rho idx); apply lval_eq_true in IHILDerivation.
    change (truth B (lval M p rho sigma idx = lval M r rho sigma idx) =
      truth B (lval M q rho sigma idx = lval M r rho sigma idx)); rewrite IHILDerivation; reflexivity.
Qed.
End Soundness.

(* Gallin p. 20 defines Gamma |- p by a theorem formed from a finite
   list of Gamma's formulas as nested implications. A hypothesis is NOT
   introduced into the unrestricted theorem replacement rules. *)
Fixpoint il_implication_chain {G} (ps : list (ltm G t)) (q : ltm G t) : ltm G t :=
  match ps with [] => q | p :: rest => limp p (il_implication_chain rest q) end.
Definition ILFrom {G} (Gamma : ltm G t -> Prop) (q : ltm G t) : Type :=
  { ps : list (ltm G t) & (Forall Gamma ps * ILDerivation (il_implication_chain ps q))%type }.
Theorem il_from_assumptions_sound G (Gamma : ltm G t -> Prop) q (H : ILFrom Gamma q)
  M sigma rho i :
  (forall p, Gamma p -> lval M p rho sigma i = true) -> lval M q rho sigma i = true.
Proof.
  destruct H as [ps [HP HD]]; intro HG.
  pose proof (il_derivations_sound sigma HD rho i) as HT.
  clear HD; induction HP; cbn [il_implication_chain] in HT; auto.
  rewrite lval_imp, (HG x H) in HT; cbn in HT; apply IHHP; exact HT.
Qed.
