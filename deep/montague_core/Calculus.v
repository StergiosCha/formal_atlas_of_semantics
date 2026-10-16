(* Object-language derivability for C, separate from Coq's own entailment.
   Contexts are split into typed variables G and true-formula assumptions H.
   Contexts.v proves correspondence with an independently defined intrinsic
   interleaved calculus. Adequacy for the source's named typing judgments is
   still separate. Generalization weakens H: the eigenvariable is fresh.
   Classical C adds ONE explicit rule: double-negation elimination. *)
From Coq Require Import List.
From MontagueProof Require Import Syntax Models.
Import ListNotations.
Set Implicit Arguments.

Inductive logic := constructive | classical.
Definition permits_classical (L : logic) := L = classical -> ClassicalTruth.

Section ProofSystem.
Variable symbol : ty -> Type.
Variable L : logic.

Inductive derives : forall G, list (tm symbol G truth) -> tm symbol G truth -> Prop :=
| d_assume : forall G H (p : tm symbol G truth), In p H -> derives H p
| d_imp_intro : forall G H (p q : tm symbol G truth),
    derives (p :: H) q -> derives H (Imp p q)
| d_imp_elim : forall G H (p q : tm symbol G truth),
    derives H (Imp p q) -> derives H p -> derives H q
| d_all_intro : forall G a (H : list (tm symbol G truth)) (p : tm symbol (a :: G) truth),
    derives (map (@weaken symbol G a truth) H) p -> derives H (All p)
| d_all_elim : forall G a H (p : tm symbol (a :: G) truth) (u : tm symbol G a),
    derives H (All p) -> derives H (instantiate u p)
| d_conversion : forall G H (p q : tm symbol G truth),
    derives H p -> beta p q -> derives H q
| d_double_negation : forall G H (p : tm symbol G truth),
    L = classical -> derives H (neg (neg p)) -> derives H p.

Theorem assumption_weakening : forall G H (p : tm symbol G truth),
  derives H p -> forall H', incl H H' -> derives H' p.
Proof.
  intros G H p D; induction D; intros H' Inc.
  - apply d_assume; apply Inc; assumption.
  - apply d_imp_intro; apply IHD. intros r [E | Hin].
    + left; exact E.
    + right; apply Inc; exact Hin.
  - eapply d_imp_elim; [apply IHD1 | apply IHD2]; exact Inc.
  - apply d_all_intro; apply IHD. apply incl_map; exact Inc.
  - apply d_all_elim; apply IHD; exact Inc.
  - eapply d_conversion; [apply IHD; exact Inc | eassumption].
  - apply d_double_negation; [assumption | apply IHD; exact Inc].
Qed.

Theorem cut : forall G H (p q : tm symbol G truth),
  derives H p -> derives (p :: H) q -> derives H q.
Proof.
  intros G H p q Dp Dq.
  eapply d_imp_elim; [apply d_imp_intro; exact Dq | exact Dp].
Qed.

Theorem derivation_sound (FE : FunExt) : forall G H (p : tm symbol G truth),
  derives H p -> forall (M : model symbol) (rho : env M G),
  permits_classical L -> satisfies M rho H -> eval M p rho.
Proof.
  intros G H p D; induction D; intros M rho CL Sat; cbn.
  - apply Sat; assumption.
  - intro Hp; apply IHD; [exact CL |]. intros r [E | Hin].
    + subst; exact Hp.
    + apply Sat; exact Hin.
  - exact (IHD1 M rho CL Sat (IHD2 M rho CL Sat)).
  - intro x; apply IHD; [exact CL |]. intros r Hin.
    apply in_map_iff in Hin; destruct Hin as [q [E Hin]]; subst r.
    rewrite (eval_weaken (M:=M) FE). apply Sat; exact Hin.
  - rewrite (eval_instantiate (M:=M) FE). apply IHD; assumption.
  - rewrite <- (beta_sound (M:=M) FE H0 rho). apply IHD; assumption.
  - destruct (CL H0 (eval M p rho)) as [Hp | Hnp]; [exact Hp |].
    pose proof (IHD M rho CL Sat) as Hnn.
    apply (proj1 (neg_meaning (M:=M) (neg p) rho)) in Hnn.
    exfalso; apply Hnn; apply (proj2 (neg_meaning (M:=M) p rho)); exact Hnp.
Qed.

End ProofSystem.

Arguments derives {symbol} L {G} _ _.

Theorem constructive_in_classical : forall symbol G H (p : tm symbol G truth),
  derives constructive H p -> derives classical H p.
Proof.
  intros symbol G H p D; induction D.
  - apply d_assume; assumption.
  - apply d_imp_intro; assumption.
  - eapply d_imp_elim; eassumption.
  - apply d_all_intro; assumption.
  - apply d_all_elim; assumption.
  - eapply d_conversion; eassumption.
  - discriminate.
Qed.

Theorem constructive_sound (FE : FunExt) : forall symbol G H (p : tm symbol G truth),
  derives constructive H p -> consequence H p.
Proof.
  intros symbol G H p D M rho Sat.
  eapply derivation_sound; [exact FE | exact D | | exact Sat].
  unfold permits_classical; discriminate.
Qed.

Theorem classical_sound (FE : FunExt) (CL : ClassicalTruth) :
  forall symbol G H (p : tm symbol G truth),
  derives classical H p -> consequence H p.
Proof.
  intros symbol G H p D M rho Sat.
  eapply derivation_sound; [exact FE | exact D | | exact Sat].
  intros _; exact CL.
Qed.

(* Refutation requires an actual model and assignment, not a failed tactic. *)
Theorem countermodel_blocks_derivation (FE : FunExt) :
  forall symbol L G H (p : tm symbol G truth) (M : model symbol) (rho : env M G),
  permits_classical L -> satisfies M rho H -> ~ eval M p rho ->
  ~ derives L H p.
Proof.
  intros symbol L G H p M rho CL Sat Hnot D.
  apply Hnot; eapply derivation_sound; eassumption.
Qed.
