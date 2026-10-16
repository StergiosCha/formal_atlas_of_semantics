(* Equality used to merge discovered analyses under the explicit PTQ
   postulates. It does not apply to seek, attitudes or control predicates. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning
  Postulates Reductions ReadingForms ReadingClassification.
Import ListNotations.
Set Implicit Arguments.

Lemma extensional_object_lifting M (A : admissible M) v (O : extensional_tv v) Q x i :
  word_value M (ltv v) i Q x =
  Q i (fun j y => word_value M (ltv v) j (fun k P => P k y) x).
Proof.
  rewrite (@tv_extensional_reduction M A v O); f_equal.
  apply (function_extensionality M); intro j; apply (function_extensionality M); intro y.
  symmetry; apply tv_singleton_reduction; assumption.
Qed.

Lemma quantified_object_lifting M (A : admissible M) v (O : extensional_tv v) d C x i :
  word_value M (ltv v) i (fun j => dvalue M d (C j) j) x =
  dvalue M d (C i) i (fun j y => word_value M (ltv v) j (fun k P => P k y) x).
Proof. exact (@extensional_object_lifting M A v O (fun j => dvalue M d (C j) j) x i). Qed.

Ltac reading_congruence M A :=
  first [reflexivity |
    progress setoid_rewrite (@quantified_object_lifting M A find I); reading_congruence M A |
    progress setoid_rewrite (@quantified_object_lifting M A love I); reading_congruence M A |
    lazymatch goal with |- @eq (forall _ : _, _) _ _ =>
      apply (function_extensionality M); intro; reading_congruence M A end |
    progress f_equal; reading_congruence M A].

Ltac normalize_discovered_reading A :=
  lazymatch goal with |- denote ?M ?u ?r ?i = denote ?M ?v ?r ?i =>
    let left := eval cbv in u in let right := eval cbv in v in
    change (denote M left r i = denote M right r i);
    cbn [denote update Nat.eqb];
    reading_congruence M A
  end.

Theorem finds_quantifier_lifting_is_sound M (A : admissible M) r i :
  denote M (s14 (s2 a_or_an (s1_word (lcn unicorn))) 0
    (s4 (s1_name john) (s5 (s1_word (ltv find)) (s1_pronoun 0)))) r i =
  denote M (s4 (s1_name john) (s5 (s1_word (ltv find))
    (s2 a_or_an (s1_word (lcn unicorn))))) r i.
Proof. normalize_discovered_reading A. Qed.
