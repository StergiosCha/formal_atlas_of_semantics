(* Diagnostic checks, NOT a new corpus formalization or a source outcome.
   Run using run_checks.sh: it compiles fresh copies of the actual inputs.
   No claims from the admitted/inconsistent parts of those inputs are used. *)
From Coq Require Import List QArith.
Require Import FCS FCS2 DonkeyScope DisCoCat.
Import ListNotations.

(* The supposedly ill-typed comprehension is an accepted definition and
   has no classical or other axiomatic dependencies. *)
Print Assumptions FCS.exists_ccp.

(* This existing contradiction depends on the invented unrestricted class
   comprehension axioms, not on Heim's semantics. *)
Print Assumptions FCS2.MorseKelley.class_comprehension_inconsistent.

Local Open Scope nat_scope.

Theorem donkey_dpl_actual_truth_conditions : forall g h,
  DonkeyScope.donkey_dpl g h <->
  g = h /\ forall f, DonkeyScope.farmer f ->
    exists d, DonkeyScope.donkey d /\
      DonkeyScope.owns f d /\ DonkeyScope.beats f d.
Proof.
  intros g h.
  unfold DonkeyScope.donkey_dpl, DonkeyScope.dpl_forall,
    DonkeyScope.dpl_and, DonkeyScope.dpl_exists, DonkeyScope.atomic,
    DonkeyScope.farmer_atom, DonkeyScope.donkey_atom,
    DonkeyScope.owns_atom, DonkeyScope.beats_atom.
  split.
  - intros [E H]; split; [exact E |].
    intros f Hf.
    assert (Hpre : exists k, DonkeyScope.update g 0 f = k /\
      DonkeyScope.farmer (DonkeyScope.update g 0 f 0)).
    { exists (DonkeyScope.update g 0 f); split; [reflexivity | exact Hf]. }
    destruct (H f Hpre) as
      [out [mid [[d [inn [[Ei Hd] [Em Ho]]]] [Eo Hb]]]].
    subst inn; subst mid; subst out.
    cbn [DonkeyScope.update] in Hd, Ho, Hb.
    exists d; repeat split; assumption.
  - intros [E H]; split; [exact E |].
    intros f [k [Ek Hf]].
    cbn [DonkeyScope.update] in Hf.
    destruct (H f Hf) as [d [Hd [Ho Hb]]].
    exists (DonkeyScope.update (DonkeyScope.update g 0 f) 1 d).
    exists (DonkeyScope.update (DonkeyScope.update g 0 f) 1 d).
    split.
    + exists d.
      exists (DonkeyScope.update (DonkeyScope.update g 0 f) 1 d).
      cbn [DonkeyScope.update]; repeat split; assumption.
    + cbn [DonkeyScope.update]; split; [reflexivity | exact Hb].
Qed.

(* A non-owning farmer suffices to refute the implemented sentence. *)
Theorem nonowner_refutes_implemented_donkey : forall g h f,
  DonkeyScope.farmer f ->
  (forall d, ~ DonkeyScope.owns f d) ->
  ~ DonkeyScope.donkey_dpl g h.
Proof.
  intros g h f Hf Hnone H.
  destruct (proj1 (donkey_dpl_actual_truth_conditions g h) H) as [_ Howns].
  destruct (Howns f Hf) as [d [_ [Ho _]]].
  exact (Hnone d Ho).
Qed.

(* With an empty ownership relation, the intended strong reading is true
   but the implemented reading is false as soon as there is a farmer.
   This is conditional on a model signature, not on any choice axiom. *)
Theorem empty_ownership_separates_readings : forall g f,
  DonkeyScope.farmer f ->
  (forall x d, ~ DonkeyScope.owns x d) ->
  DonkeyScope.unselective_binding /\ ~ DonkeyScope.donkey_dpl g g.
Proof.
  intros g f Hf Hnone; split.
  - unfold DonkeyScope.unselective_binding.
    intros x d _ _ Ho; exfalso; exact (Hnone x d Ho).
  - exact (nonowner_refutes_implemented_donkey g g f Hf (Hnone f)).
Qed.

Print Assumptions donkey_dpl_actual_truth_conditions.
Print Assumptions nonowner_refutes_implemented_donkey.
Print Assumptions empty_ownership_separates_readings.

Module SimilarityCheck.
Import DisCoCat.Examples DisCoCat.ExModel.
Local Open Scope Q_scope.

Definition love_sentence :=
  meaning dim2 tv_red [(nty, john); (tv, loves); (nty, mary)].
Definition graded_sentence :=
  meaning dim2 tv_red [(nty, john); (tv, likes_g); (nty, mary)].

(* Squaring Def 5.1 avoids square roots. This expression represents
   cosine squared only for nonzero vectors; the next lemma verifies that
   condition for these particular source/example vectors. *)
Definition cosine_squared (v w : nat -> nat -> Q) : Q :=
  (inner 2 v w * inner 2 v w) / (inner 2 v v * inner 2 w w).

Theorem actual_vector_values :
  Qred (inner 2 love_sentence love_sentence) = 1 /\
  Qred (inner 2 graded_sentence graded_sentence) = 5 # 8 /\
  Qred (inner 2 love_sentence graded_sentence) = 3 # 4.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem normalized_square_is_nine_tenths :
  Qred (cosine_squared love_sentence graded_sentence) = 9 # 10.
Proof. vm_compute; reflexivity. Qed.

Theorem raw_square_is_nine_sixteenths :
  Qred (inner 2 love_sentence graded_sentence *
        inner 2 love_sentence graded_sentence) = 9 # 16.
Proof. vm_compute; reflexivity. Qed.

Theorem raw_similarity_is_not_normalized :
  ~ (cosine_squared love_sentence graded_sentence ==
     inner 2 love_sentence graded_sentence *
     inner 2 love_sentence graded_sentence).
Proof. vm_compute; discriminate. Qed.

Print Assumptions actual_vector_values.
Print Assumptions normalized_square_is_nine_tenths.
Print Assumptions raw_square_is_nine_sixteenths.
Print Assumptions raw_similarity_is_not_normalized.
End SimilarityCheck.

Print Assumptions DisCoCat.F_deq.
Print Assumptions DisCoCat.meaning_deq.
