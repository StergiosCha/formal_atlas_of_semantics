(* Reading exhaustiveness means semantic coverage of ALL successful trees,
   not a finite depth search and not agreement in a single sample model. *)
From Coq Require Import List Bool Strings.String.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning
  Postulates Surface Catalogue SurfaceAmendment.
Import ListNotations.
Set Implicit Arguments.

Definition reading_equivalent (u v : tree ct) :=
  forall M, admissible M -> forall sigma i,
    eval M (translate_closed u) (empty_env M) sigma i =
    eval M (translate_closed v) (empty_env M) sigma i.

Definition reading_exhaustive render (text : list string) (candidates : list (tree ct)) :=
  forall u : tree ct, render u = Some text ->
    exists v, In v candidates /\ reading_equivalent u v.

Definition catalogue_exhaustive render entries :=
  Forall (fun entry => reading_exhaustive render (fst entry) (snd entry)) entries.

Lemma reading_equivalent_refl u : reading_equivalent u u.
Proof. intros M A sigma i; reflexivity. Qed.
Lemma reading_equivalent_sym u v : reading_equivalent u v -> reading_equivalent v u.
Proof. intros H M A sigma i; symmetry; apply H; exact A. Qed.
Lemma reading_equivalent_trans u v w :
  reading_equivalent u v -> reading_equivalent v w -> reading_equivalent u w.
Proof. intros H K M A sigma i; rewrite (H M A sigma i); apply K; exact A. Qed.

Lemma reading_exhaustive_monotone render text small large :
  (forall u, In u small -> In u large) ->
  reading_exhaustive render text small -> reading_exhaustive render text large.
Proof. intros I H u S; destruct (H u S) as [v [V E]]; exists v; auto. Qed.

Lemma separating_model_refutes_equivalence u v M : admissible M ->
  forall sigma i, eval M (translate_closed u) (empty_env M) sigma i <>
    eval M (translate_closed v) (empty_env M) sigma i -> ~ reading_equivalent u v.
Proof. intros A sigma i N E; apply N; apply E; exact A. Qed.

Definition only_unicorn_referential render (text : list string) :=
  forall u : tree ct, render u = Some text ->
    forall M, admissible M -> forall r i,
      denote M u r i = true -> exists x, word_value M (lcn unicorn) i x = true.
