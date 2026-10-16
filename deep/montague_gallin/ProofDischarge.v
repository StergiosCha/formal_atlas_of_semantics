(* Finite implication discharge, following Gallin p. 20. This adds no
   hypothesis constructor to either theorem calculus. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Target Translation Minimal Calculus
  ILCore ILCalculus ILProofTranslation ILFullProofTranslation.
Import ListNotations.
Set Implicit Arguments.

Fixpoint ty2_implication_chain {S P G} (ps : list (ctm S P G gt)) (q : ctm S P G gt) :=
  match ps with [] => q | p :: rest => cimp p (ty2_implication_chain rest q) end.
Definition Ty2From {S P G} (Gamma : ctm S P G gt -> Prop) (q : ctm S P G gt) : Type :=
  { ps : list (ctm S P G gt) & (Forall Gamma ps * Derivation (ty2_implication_chain ps q))%type }.

Theorem ty2_from_assumptions_sound {S P E I} (B : BooleanTruth) (FE : FunExt)
  (lex : forall a, S a -> value_domain E I a) (theta : forall a, P a -> value_domain E I a)
  G (Gamma : ctm S P G gt -> Prop) q (H : Ty2From Gamma q) rho :
  (forall p, Gamma p -> ceval B lex theta p rho = true) -> ceval B lex theta q rho = true.
Proof.
  destruct H as [ps [HP HD]]; intro HG.
  pose proof (ty2_derivations_sound B FE lex theta HD rho) as HT.
  clear HD; induction HP; cbn [ty2_implication_chain] in HT; auto.
  rewrite ceval_imp in HT by exact FE.
  rewrite (HG x H) in HT; cbn in HT; apply IHHP; exact HT.
Qed.

Definition compiled_premises {G} (Gamma : ltm G t -> Prop)
  (p : ctm source_symbol source_parameter (gs :: map translate_type G) gt) : Prop :=
  exists q, Gamma q /\ p = il_at q.
Lemma compile_implication_chain G (ps : list (ltm G t)) q :
  il_at (il_implication_chain ps q) = ty2_implication_chain (map (@il_at G t) ps) (il_at q).
Proof. induction ps; cbn [il_implication_chain ty2_implication_chain map];
  [reflexivity | rewrite il_at_implication, IHps; reflexivity]. Qed.

Definition compile_il_from G (Gamma : ltm G t -> Prop) q (H : ILFrom Gamma q) :
  Ty2From (compiled_premises Gamma) (il_at q).
Proof.
  destruct H as [ps [HP HD]]; exists (map (@il_at G t) ps); split.
  - clear HD; induction HP; cbn [map]; constructor.
    + exists x; split; [exact H | reflexivity].
    + exact IHHP.
  - rewrite <- compile_implication_chain; exact (compile_il_proof HD).
Defined.
