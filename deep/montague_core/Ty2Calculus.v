(* C-style rules over e,t,s. Necessity is world quantification, not an
   unrestricted necessitation rule from arbitrary local assumptions. *)
From Coq Require Import List Bool.
From MontagueProof Require Import Models Calculus BooleanModels Ty2Syntax Ty2Models.
Import ListNotations.
Set Implicit Arguments.

Section Rules.
Variable symbol : wty -> Type.
Variable L : logic.
Inductive wderives : forall G, list (wtm symbol G wt) -> wtm symbol G wt -> Prop :=
| wd_assume : forall G H (p : wtm symbol G wt), In p H -> wderives H p
| wd_imp_intro : forall G H (p q : wtm symbol G wt),
    wderives (p :: H) q -> wderives H (WImp p q)
| wd_imp_elim : forall G H (p q : wtm symbol G wt),
    wderives H (WImp p q) -> wderives H p -> wderives H q
| wd_all_intro : forall G a (H : list (wtm symbol G wt)) (p : wtm symbol (a :: G) wt),
    wderives (map (@wweaken symbol G a wt) H) p -> wderives H (WAll p)
| wd_all_elim : forall G a H (p : wtm symbol (a :: G) wt) u,
    wderives H (WAll p) -> wderives H (winstantiate u p)
| wd_conversion : forall G H (p q : wtm symbol G wt),
    wderives H p -> wbeta p q -> wderives H q
| wd_double_negation : forall G H (p : wtm symbol G wt),
    L = classical -> wderives H (wneg (wneg p)) -> wderives H p.
End Rules.
Arguments wderives {symbol} L {G} _ _.

Definition wsatisfies {symbol G} (M : wmodel symbol) (rho : wenv M G)
  (H : list (wtm symbol G wt)) := forall p, In p H -> weval M p rho = true.
Arguments wsatisfies {symbol G} M rho H.
Definition wconsequence {symbol G} (H : list (wtm symbol G wt)) (p : wtm symbol G wt) :=
  forall (M : wmodel symbol) rho, wsatisfies M rho H -> weval M p rho = true.

Theorem world_derivation_sound (FE : FunExt) : forall symbol L G H (p : wtm symbol G wt),
  wderives L H p -> wconsequence H p.
Proof.
  intros symbol L G H p D; induction D; intros M rho Sat.
  - apply Sat; assumption.
  - cbn; apply bimp_spec; intro Hp; apply IHD.
    intros r [E | Hin]; [subst; exact Hp | apply Sat; exact Hin].
  - pose proof (IHD1 M rho Sat) as HI; cbn in HI.
    apply (proj1 (bimp_spec _ _) HI); apply IHD2; exact Sat.
  - cbn; apply wforall_spec; intro x; apply IHD.
    intros r Hin; apply in_map_iff in Hin; destruct Hin as [q [E Hin]]; subst r.
    rewrite (weval_weaken FE); apply Sat; exact Hin.
  - rewrite (weval_instantiate FE).
    pose proof (IHD M rho Sat) as HA.
    exact (proj1 (wforall_spec (wquantifiers M) _ _) HA (weval M u rho)).
  - rewrite <- (wbeta_sound FE H0 rho); apply IHD; exact Sat.
  - pose proof (IHD M rho Sat) as Hnn.
    rewrite !wneg_value, negb_involutive in Hnn; exact Hnn.
Qed.

Theorem world_countermodel_blocks_derivation (FE : FunExt) :
  forall symbol L G H (p : wtm symbol G wt) (M : wmodel symbol) (rho : wenv M G),
  wsatisfies M rho H -> weval M p rho = false -> ~ wderives L H p.
Proof.
  intros symbol L G H p M rho Sat FalseValue D.
  pose proof (world_derivation_sound FE D (M:=M) (rho:=rho) Sat) as TrueValue.
  rewrite FalseValue in TrueValue; discriminate.
Qed.
