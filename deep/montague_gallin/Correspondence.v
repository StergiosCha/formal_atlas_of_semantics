(* Consequence over ALL independently chosen coherent target valuations,
   not just an image-defined target class. PTQ meaning postulates are
   imposed as translated target formulas, not as a source-model field. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models Named Postulates PostulateFormulas.
From MontagueGallin Require Import Types Target Translation Examples Independent.
Import ListNotations.
Set Implicit Arguments.

Lemma postulate_family_extensional (P Q : ntm t -> Prop) :
  (forall p, P p <-> Q p) -> postulate_family P <-> postulate_family Q.
Proof. unfold postulate_family; firstorder. Qed.

Definition target_postulates_at F (N : coherent_model F) (theta : coherent_assignment F) i :=
  postulate_family (fun p =>
    coherent_eval N theta (translate_intension (embed_named p)) (gempty F) i = true).
Definition target_admissible F (N : coherent_model F) :=
  forall theta i, target_postulates_at N theta i.

Theorem translated_postulates_exact F (N : coherent_model F) theta i :
  target_postulates_at N theta i <-> admissible (reconstruct_model N).
Proof.
  unfold target_postulates_at.
  transitivity (postulate_family (fun p => eval (reconstruct_model N)
    (embed_named p) (empty_env _) (reconstruct_assignment N theta) i = true)).
  - apply postulate_family_extensional; intro p.
    rewrite backward_preservation; reflexivity.
  - apply compiled_postulates_exact.
Qed.
Theorem admissible_model_correspondence F (N : coherent_model F) :
  target_admissible N <-> admissible (reconstruct_model N).
Proof.
  split.
  - intro H; destruct (index_inhabited F) as [i].
    apply (proj1 (translated_postulates_exact N (reference_assignment N i) i)); apply H.
  - intros H theta i; apply translated_postulates_exact; exact H.
Qed.

Theorem embed_preserves_admissibility M : admissible M -> target_admissible (embed_model M).
Proof.
  intros HM theta i; unfold target_postulates_at.
  assert (K : forall p : ntm t, coherent_eval (embed_model M) theta
    (translate_intension (embed_named p)) (gempty (carrier M)) i = true <->
    eval M (embed_named p) (empty_env M)
      (reconstruct_assignment (embed_model M) theta) i = true).
  { intro p; rewrite embedded_arbitrary_assignment, closed_preservation; reflexivity. }
  apply (proj2 (postulate_family_extensional
    (fun p => coherent_eval (embed_model M) theta
      (translate_intension (embed_named p)) (gempty (carrier M)) i = true)
    (fun p => eval M (embed_named p) (empty_env M)
      (reconstruct_assignment (embed_model M) theta) i = true) K)).
  apply compiled_postulates_exact; exact HM.
Qed.

Definition coherent_consequence (ps : list (tm [] t)) (q : tm [] t) :=
  forall F (N : coherent_model F) (theta : coherent_assignment F) i,
    (forall p, In p ps -> coherent_eval N theta (translate_intension p) (gempty F) i = true) ->
    coherent_eval N theta (translate_intension q) (gempty F) i = true.
Definition admissible_target_consequence (ps : list (tm [] t)) (q : tm [] t) :=
  forall F (N : coherent_model F), target_admissible N -> forall theta i,
    (forall p, In p ps -> coherent_eval N theta (translate_intension p) (gempty F) i = true) ->
    coherent_eval N theta (translate_intension q) (gempty F) i = true.

Theorem independent_consequence_correspondence ps q :
  coherent_consequence ps q <-> source_consequence (fun _ => True) ps q.
Proof.
  split.
  - intros H M HM sigma i HP.
    assert (Q : coherent_eval (embed_model M) (target_free sigma)
      (translate_intension q) (gempty (carrier M)) i = true).
    { apply H; intros p Hp; rewrite forward_preservation; apply HP; exact Hp. }
    rewrite forward_preservation in Q; exact Q.
  - intros H F N theta i HP; rewrite backward_preservation.
    apply H; [exact I |].
    intros p Hp; specialize (HP p Hp); rewrite backward_preservation in HP; exact HP.
Qed.
Theorem admissible_consequence_correspondence ps q :
  admissible_target_consequence ps q <-> source_consequence admissible ps q.
Proof.
  split.
  - intros H M HM sigma i HP.
    assert (Q : coherent_eval (embed_model M) (target_free sigma)
      (translate_intension q) (gempty (carrier M)) i = true).
    { apply H; [apply embed_preserves_admissibility; exact HM |].
      intros p Hp; rewrite forward_preservation; apply HP; exact Hp. }
    rewrite forward_preservation in Q; exact Q.
  - intros H F N HN theta i HP; rewrite backward_preservation.
    apply H; [apply admissible_model_correspondence; exact HN |].
    intros p Hp; specialize (HP p Hp); rewrite backward_preservation in HP; exact HP.
Qed.

Definition source_satisfiable (ps : list (tm [] t)) :=
  exists M, admissible M /\ exists sigma i,
    forall p, In p ps -> eval M p (empty_env M) sigma i = true.
Definition target_satisfiable (ps : list (tm [] t)) :=
  exists F (N : coherent_model F), target_admissible N /\ exists theta i,
    forall p, In p ps -> coherent_eval N theta (translate_intension p) (gempty F) i = true.
Theorem admissible_satisfiability_correspondence ps :
  source_satisfiable ps <-> target_satisfiable ps.
Proof.
  split.
  - intros [M [HM [sigma [i HP]]]].
    exists (carrier M), (embed_model M); split.
    + apply embed_preserves_admissibility; exact HM.
    + exists (target_free sigma), i; intros p Hp.
      rewrite forward_preservation; apply HP; exact Hp.
  - intros [F [N [HN [theta [i HP]]]]].
    exists (reconstruct_model N); split.
    + apply admissible_model_correspondence; exact HN.
    + exists (reconstruct_assignment N theta), i; intros p Hp.
      specialize (HP p Hp); rewrite backward_preservation in HP; exact HP.
Qed.
