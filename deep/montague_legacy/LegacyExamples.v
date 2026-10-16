(* Regressions about the actual legacy syntax/evaluator. Distinct times,
   worlds and order edges are hypotheses, not newly postulated axioms. *)
From Coq Require Import List.
From MontagueProof Require Import Models.
From MontagueLegacy Require Import IndexSyntax IndexModels LegacyTranslation.
Import ListNotations.
Set Implicit Arguments.

Definition legacy_atom : Old.IL [Old.ty_s Old.ty_t] Old.ty_t :=
  Old.down (@Old.var_z [] (Old.ty_s Old.ty_t)).
Definition at_time (t : Old.Time) : Old.Env [Old.ty_s Old.ty_t] :=
  @Old.env_cons (Old.ty_s Old.ty_t) [] (fun i : Old.Index => snd i = t) tt.

Example no_tense_still_allows_time_dependence (w : Old.World) (t0 t1 : Old.Time) :
  t0 <> t1 -> Old.eval legacy_atom (at_time t0) (w,t0) /\
    ~ Old.eval legacy_atom (at_time t0) (w,t1).
Proof. cbn; intros H; split; [reflexivity | intros E; apply H; symmetry; exact E]. Qed.

Example legacy_necessity_holds_time_fixed (w : Old.World) (t0 : Old.Time) :
  Old.eval (Old.nec_ legacy_atom) (at_time t0) (w,t0).
Proof. intros w'; reflexivity. Qed.

Example necessity_is_not_all_index_quantification (w : Old.World) (t0 t1 : Old.Time) :
  t0 <> t1 -> Old.eval (Old.nec_ legacy_atom) (at_time t0) (w,t0) /\
    ~ (forall i, Old.eval legacy_atom (at_time t0) i).
Proof.
  intro H; split; [apply legacy_necessity_holds_time_fixed |].
  intro A; specialize (A (w,t1)); apply H; symmetry; exact A.
Qed.

Example translated_necessity_keeps_time (FE : FunExt) (w : Old.World) (t0 : Old.Time) :
  target_eval (legacy_as_index_function (Old.nec_ legacy_atom))
    (canonical_env _ (at_time t0)) (w,t0).
Proof. apply (proj2 (legacy_truth_preservation FE _ _ _)); apply legacy_necessity_holds_time_fixed. Qed.

Example translated_atom_retains_time_dependence (FE : FunExt) (w : Old.World) (t0 t1 : Old.Time) :
  t0 <> t1 ->
  target_eval (legacy_as_index_function legacy_atom) (canonical_env _ (at_time t0)) (w,t0) /\
  ~ target_eval (legacy_as_index_function legacy_atom) (canonical_env _ (at_time t0)) (w,t1).
Proof.
  intro H; repeat rewrite (legacy_open_preservation FE).
  exact (no_tense_still_allows_time_dependence w H).
Qed.

Example intension_abstracts_over_time_too (w : Old.World) (t0 t1 : Old.Time) :
  t0 <> t1 ->
  Old.eval (Old.up legacy_atom) (at_time t0) (w,t0) (w,t0) /\
  ~ Old.eval (Old.up legacy_atom) (at_time t0) (w,t0) (w,t1).
Proof. apply no_tense_still_allows_time_dependence. Qed.

Definition at_index (i : Old.Index) : Old.Env [Old.ty_s Old.ty_t] :=
  @Old.env_cons (Old.ty_s Old.ty_t) [] (fun j : Old.Index => j = i) tt.

Example future_keeps_world_and_order (w : Old.World) (t0 t1 : Old.Time) :
  Old.time_lt t0 t1 -> Old.eval (Old.will_ legacy_atom) (at_index (w,t1)) (w,t0).
Proof. intro H; exists t1; split; [exact H | reflexivity]. Qed.

Example past_keeps_world_and_order (w : Old.World) (t0 t1 : Old.Time) :
  Old.time_lt t0 t1 -> Old.eval (Old.has_ legacy_atom) (at_index (w,t0)) (w,t1).
Proof. intro H; exists t0; split; [exact H | reflexivity]. Qed.

Example reversing_future_order_changes_predictions (w : Old.World) (t0 t1 : Old.Time) :
  Old.time_lt t0 t1 -> ~ Old.time_lt t1 t0 ->
  Old.eval (Old.will_ legacy_atom) (at_time t1) (w,t0) /\
  ~ (exists t', Old.time_lt t' t0 /\ Old.eval legacy_atom (at_time t1) (w,t')).
Proof.
  intros F B; split.
  - exists t1; split; [exact F | reflexivity].
  - intros [t' [L E]]; cbn in E; subst t'; contradiction.
Qed.

Example translated_future_and_past (FE : FunExt) (w : Old.World) (t0 t1 : Old.Time) :
  Old.time_lt t0 t1 ->
  target_eval (legacy_as_index_function (Old.will_ legacy_atom))
    (canonical_env _ (at_index (w,t1))) (w,t0) /\
  target_eval (legacy_as_index_function (Old.has_ legacy_atom))
    (canonical_env _ (at_index (w,t0))) (w,t1).
Proof.
  intro H; repeat rewrite (legacy_open_preservation FE); split;
    [apply future_keeps_world_and_order | apply past_keeps_world_and_order]; exact H.
Qed.

Definition legacy_reflexive : Old.IL [] Old.ty_t :=
  Old.eq_ (Old.c_john []) (Old.c_john []).

Example weakening_shifts_a_whole_term_not_only_a_variable :
  compile_legacy (@Old.var_s [] Old.ty_t Old.ty_e legacy_reflexive)
    (pz,tt) (@PVar legacy_symbol [pe;pi] pi (pvs pz)) =
  compile_legacy legacy_reflexive tt (@PVar legacy_symbol [pe;pi] pi (pvs pz)).
Proof. reflexivity. Qed.

Example translated_primitive_equality (FE : FunExt) (i : Old.Index) :
  target_eval (legacy_as_index_function legacy_reflexive) empty_target_env i.
Proof. exact (proj2 (@legacy_truth_preservation FE [] legacy_reflexive tt i) eq_refl). Qed.

Definition legacy_higher_order_identity : Old.IL [] Old.ty_t :=
  Old.forall_ (Old.forall_
    (Old.imp_ (Old.app (@Old.var_s [Old.ty_arrow Old.ty_e Old.ty_t]
      (Old.ty_arrow Old.ty_e Old.ty_t) Old.ty_e (@Old.var_z [] (Old.ty_arrow Old.ty_e Old.ty_t)))
      (@Old.var_z [Old.ty_arrow Old.ty_e Old.ty_t] Old.ty_e))
      (Old.app (@Old.var_s [Old.ty_arrow Old.ty_e Old.ty_t]
      (Old.ty_arrow Old.ty_e Old.ty_t) Old.ty_e (@Old.var_z [] (Old.ty_arrow Old.ty_e Old.ty_t)))
      (@Old.var_z [Old.ty_arrow Old.ty_e Old.ty_t] Old.ty_e)))).

Example translated_higher_order_quantifiers (FE : FunExt) (i : Old.Index) :
  target_eval (legacy_as_index_function legacy_higher_order_identity) empty_target_env i.
Proof.
  apply (proj2 (@legacy_truth_preservation FE [] legacy_higher_order_identity tt i)); cbn; auto.
Qed.

Definition legacy_frozen : Old.IL [Old.ty_s Old.ty_e] (Old.ty_s Old.ty_e) :=
  Old.app (Old.lam (Old.up (@Old.var_z [Old.ty_s Old.ty_e] Old.ty_e)))
    (Old.down (@Old.var_z [] (Old.ty_s Old.ty_e))).
Definition legacy_recomputed : Old.IL [Old.ty_s Old.ty_e] (Old.ty_s Old.ty_e) :=
  Old.up (Old.down (@Old.var_z [] (Old.ty_s Old.ty_e))).

Example actual_legacy_freezing_distinction (c : Old.Index -> Old.Entity) i j :
  c i <> c j ->
  Old.eval legacy_frozen (@Old.env_cons (Old.ty_s Old.ty_e) [] c tt) i j <>
  Old.eval legacy_recomputed (@Old.env_cons (Old.ty_s Old.ty_e) [] c tt) i j.
Proof. exact (fun H => H). Qed.

Example translated_legacy_freezing_distinction (FE : FunExt)
  (c : Old.Index -> Old.Entity) i j : c i <> c j ->
  target_eval (legacy_as_index_function legacy_frozen)
    (canonical_env _ (@Old.env_cons (Old.ty_s Old.ty_e) [] c tt)) i j <>
  target_eval (legacy_as_index_function legacy_recomputed)
    (canonical_env _ (@Old.env_cons (Old.ty_s Old.ty_e) [] c tt)) i j.
Proof.
  intro H; repeat rewrite (legacy_open_preservation FE); exact H.
Qed.
