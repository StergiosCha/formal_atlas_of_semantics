(* Standard models for Gallin's untensed comparison. Every independent
   target model is allowed: no temporal coherence or lexical postulates.
   The two extra temporal symbols in the shared signature are unused. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Target Translation Minimal Independent MinimalCorrespondence
  Untensed UntensedTranslation.
Import ListNotations.
Set Implicit Arguments.

Definition il_minimal_translate {G a} (p : itm G a) :=
  eliminate (translate_intension (embed_il p)).
Definition il_target_lex M a (c : source_symbol a) :
  value_domain (il_entities M) (il_indices M) a :=
  match c in source_symbol a return value_domain (il_entities M) (il_indices M) a with
  | IndexedConstant a n => fun i => il_lift (il_entities M) (il_indices M) a (il_constants M a n i)
  | FutureRelation | PastRelation => fun _ _ => false
  end.
Definition il_target (M : il_model) : standard_model source_symbol :=
  {| standard_entities := il_entities M; standard_indices := il_indices M;
     entities_inhabited := il_entities_inhabited M; indices_inhabited := il_indices_inhabited M;
     standard_truth := il_truth M; standard_extensionality := il_extensionality M;
     standard_lex := il_target_lex M |}.
Definition il_target_assignment M (sigma : il_free_env M) : standard_assignment (il_target M) source_parameter :=
  fun a v => match v in source_parameter a return value_domain (il_entities M) (il_indices M) a with
  | SourceFree b n => il_lift (il_entities M) (il_indices M) b (sigma b n)
  end.

Definition il_reconstruct (N : standard_model source_symbol) : il_model :=
  {| il_entities := standard_entities N; il_indices := standard_indices N;
     il_entities_inhabited := entities_inhabited N; il_indices_inhabited := indices_inhabited N;
     il_truth := standard_truth N; il_extensionality := standard_extensionality N;
     il_constants := fun a n i => il_lower (standard_entities N) (standard_indices N) a
       (standard_lex N _ (IndexedConstant a n) i) |}.
Definition il_reconstruct_assignment N (theta : standard_assignment N source_parameter) :
  il_free_env (il_reconstruct N) :=
  fun a n => il_lower (standard_entities N) (standard_indices N) a (theta _ (SourceFree a n)).

Theorem untensed_forward_preservation M sigma G a (p : itm G a) rho i :
  core_standard_eval (il_target M) (il_target_assignment sigma)
    (il_minimal_translate p) (il_canonical_env rho) i =
  il_lift (il_entities M) (il_indices M) a (ieval M p rho sigma i).
Proof. apply untensed_minimal_preservation; intros; reflexivity. Qed.
Theorem untensed_backward_preservation N theta G a (p : itm G a)
  (rho : il_env (il_reconstruct N) G) i :
  core_standard_eval N theta (il_minimal_translate p) (il_canonical_env rho) i =
  il_lift (standard_entities N) (standard_indices N) a
    (ieval (il_reconstruct N) p rho (il_reconstruct_assignment theta) i).
Proof.
  apply (@untensed_minimal_preservation (il_reconstruct N) (il_reconstruct_assignment theta)
    (standard_lex N) theta); intros; symmetry; apply il_lift_lower.
Qed.

Theorem il_source_constants_recovered M a n i :
  il_constants (il_reconstruct (il_target M)) a n i = il_constants M a n i.
Proof. apply il_lower_lift. Qed.
Theorem il_source_assignment_recovered M (sigma : il_free_env M) a n :
  il_reconstruct_assignment (il_target_assignment sigma) a n = sigma a n.
Proof. apply il_lower_lift. Qed.
Theorem il_target_indexed_constants_recovered N a n :
  standard_lex (il_target (il_reconstruct N)) _ (IndexedConstant a n) =
  standard_lex N _ (IndexedConstant a n).
Proof. apply (standard_extensionality N); intro i; apply il_lift_lower. Qed.
Theorem il_target_assignments_recovered N (theta : standard_assignment N source_parameter) a
  (v : source_parameter a) :
  il_target_assignment (il_reconstruct_assignment theta) v = theta a v.
Proof. destruct v; apply il_lift_lower. Qed.

(* Unlike the coherent tensed result, this only asserts recovery on
   translated untensed terms. Arbitrary temporal symbol values may differ. *)
Theorem untensed_model_roundtrip N theta G a (p : itm G a)
  (rho : il_env (il_reconstruct N) G) i :
  core_standard_eval (il_target (il_reconstruct N))
    (il_target_assignment (il_reconstruct_assignment theta))
    (il_minimal_translate p) (il_canonical_env rho) i =
  core_standard_eval N theta (il_minimal_translate p) (il_canonical_env rho) i.
Proof. rewrite untensed_forward_preservation, untensed_backward_preservation; reflexivity. Qed.

Definition il_formula := itm [] t.
Definition il_theory := il_formula -> Prop.
Definition il_standard_consequence (Gamma : il_theory) (q : il_formula) :=
  forall M sigma i,
    (forall p, Gamma p -> ieval M p (il_empty M) sigma i = true) ->
    ieval M q (il_empty M) sigma i = true.
Definition il_standard_satisfiable (Gamma : il_theory) :=
  exists M sigma i, forall p, Gamma p -> ieval M p (il_empty M) sigma i = true.

(* Predicate-defined sets allow arbitrary theories, not only finite lists.
   The displayed translation is s -> t; applying it to arbitrary i is the
   explicit-index formula A* with its index variable assigned i. *)
Definition translated_il_theory (Gamma : il_theory) (q : core_formula) :=
  exists p, Gamma p /\ q = il_minimal_translate p.
Definition ty2_standard_consequence (Delta : core_formula -> Prop) (q : core_formula) :=
  forall (N : standard_model source_symbol) (theta : standard_assignment N source_parameter) i,
    (forall p, Delta p -> core_standard_eval N theta p
      (value_empty (standard_entities N) (standard_indices N)) i = true) ->
    core_standard_eval N theta q (value_empty (standard_entities N) (standard_indices N)) i = true.
Definition ty2_standard_satisfiable (Delta : core_formula -> Prop) :=
  exists (N : standard_model source_symbol) (theta : standard_assignment N source_parameter) i,
    forall p, Delta p -> core_standard_eval N theta p
      (value_empty (standard_entities N) (standard_indices N)) i = true.

Theorem untensed_standard_consequence Gamma q :
  il_standard_consequence Gamma q <->
  ty2_standard_consequence (translated_il_theory Gamma) (il_minimal_translate q).
Proof.
  split.
  - intros H N theta i HP.
    change (core_standard_eval N theta (il_minimal_translate q)
      (il_canonical_env (il_empty (il_reconstruct N))) i = true).
    rewrite untensed_backward_preservation; cbn [il_lift il_domain_agreement cast].
    apply H; intros p Hp.
    assert (K : translated_il_theory Gamma (il_minimal_translate p)) by (exists p; auto).
    specialize (HP _ K).
    change (core_standard_eval N theta (il_minimal_translate p)
      (il_canonical_env (il_empty (il_reconstruct N))) i = true) in HP.
    rewrite untensed_backward_preservation in HP; exact HP.
  - intros H M sigma i HP.
    assert (Q : core_standard_eval (il_target M) (il_target_assignment sigma)
      (il_minimal_translate q) (il_canonical_env (il_empty M)) i = true).
    { apply H; intros p [r [Hr Ep]]; subst p.
      change (core_standard_eval (il_target M) (il_target_assignment sigma)
        (il_minimal_translate r) (il_canonical_env (il_empty M)) i = true).
      rewrite untensed_forward_preservation; apply HP; exact Hr. }
    rewrite untensed_forward_preservation in Q; exact Q.
Qed.

Theorem untensed_standard_satisfiability Gamma :
  il_standard_satisfiable Gamma <-> ty2_standard_satisfiable (translated_il_theory Gamma).
Proof.
  split.
  - intros [M [sigma [i H]]]; exists (il_target M), (il_target_assignment sigma), i.
    intros p [q [Hq Ep]]; subst p.
    change (core_standard_eval (il_target M) (il_target_assignment sigma)
      (il_minimal_translate q) (il_canonical_env (il_empty M)) i = true).
    rewrite untensed_forward_preservation; apply H; exact Hq.
  - intros [N [theta [i H]]]; exists (il_reconstruct N), (il_reconstruct_assignment theta), i.
    intros p Hp; assert (K : translated_il_theory Gamma (il_minimal_translate p)) by (exists p; auto).
    specialize (H _ K).
    change (core_standard_eval N theta (il_minimal_translate p)
      (il_canonical_env (il_empty (il_reconstruct N))) i = true) in H.
    rewrite untensed_backward_preservation in H; exact H.
Qed.
Corollary untensed_standard_validity q :
  il_standard_consequence (fun _ => False) q <->
  ty2_standard_consequence (translated_il_theory (fun _ => False)) (il_minimal_translate q).
Proof. apply untensed_standard_consequence. Qed.
