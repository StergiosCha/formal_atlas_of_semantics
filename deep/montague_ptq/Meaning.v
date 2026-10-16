(* An independent interpretation of analysis trees, following T1-T17.
   It never calls translate or eval. Correspondence with deep translation
   is proved for every tree, context, related assignment and index. *)
From Coq Require Import List Bool Arith.
From MontaguePTQ Require Import Syntax Models Grammar Translation.
Import ListNotations.
Set Implicit Arguments.

Definition pvalues (M : model) := nat -> domain (carrier M) ic.
Definition update {M} (r : pvalues M) n x : pvalues M :=
  fun m => if Nat.eqb m n then x else r m.
Definition jvalue j (p q : bool) := match j with conjunction => andb p q | disjunction => orb p q end.
Definition svalue M k (p : index (carrier M) -> bool) i :=
  match k with
  | negative => negb (p i)
  | future => truth (boolean_truth M) (exists j, before (carrier M) (snd i) j /\ p (fst i,j) = true)
  | negative_future => negb (truth (boolean_truth M) (exists j, before (carrier M) (snd i) j /\ p (fst i,j) = true))
  | perfect => truth (boolean_truth M) (exists j, before (carrier M) j (snd i) /\ p (fst i,j) = true)
  | negative_perfect => negb (truth (boolean_truth M) (exists j, before (carrier M) j (snd i) /\ p (fst i,j) = true))
  end.
Definition dvalue M d (c : domain (carrier M) ivty) i : domain (carrier M) npty :=
  fun P => match d with
  | every => truth (boolean_truth M) (forall x, orb (negb (c x)) (P i x) = true)
  | a_or_an => truth (boolean_truth M) (exists x, andb (c x) (P i x) = true)
  | the => truth (boolean_truth M) (exists y,
      andb (truth (boolean_truth M) (forall x, Bool.eqb (c x) (truth (boolean_truth M) (x = y)) = true))
        (P i y) = true)
  end.

Unset Implicit Arguments.
Fixpoint denote M {A} (u : tree A) (r : pvalues M) i : domain (carrier M) (category_type A) :=
  match u in tree A' return domain (carrier M) (category_type A') with
  | s1_word w => constants M _ (lexical_code w) i
  | s1_name n => fun P => P i (fun j => constants M e (name_code n) j)
  | s1_pronoun n => fun P => P i (r n)
  | s1_be => fun Q x => Q i (fun j y => truth (boolean_truth M) (x j = y j))
  | s1_necessarily => fun p => truth (boolean_truth M) (forall j, p j = true)
  | s2 d c => dvalue M d (denote M c r i) i
  | s3 c n p => fun x => andb (denote M c r i x) (denote M p (update r n x) i)
  | s4 p q => denote M p r i (fun j => denote M q r j)
  | s5 p q => denote M p r i (fun j => denote M q r j)
  | s6 p q => denote M p r i (fun j => denote M q r j)
  | s7 p q => denote M p r i (fun j => denote M q r j)
  | s8 p q => denote M p r i (fun j => denote M q r j)
  | s9 p q => denote M p r i (fun j => denote M q r j)
  | s10 p q => denote M p r i (fun j => denote M q r j)
  | s11 j p q => jvalue j (denote M p r i) (denote M q r i)
  | s12 j p q => fun x => jvalue j (denote M p r i x) (denote M q r i x)
  | s13 p q => fun P => orb (denote M p r i P) (denote M q r i P)
  | s14 p n q => denote M p r i (fun j x => denote M q (update r n x) j)
  | s15 p n q => fun y => denote M p r i (fun j x => denote M q (update r n x) j y)
  | s16 p n q => fun y => denote M p r i (fun j x => denote M q (update r n x) j y)
  | s17 k p q => svalue M k (fun j => denote M p r j (fun k => denote M q r k)) i
  end.
Set Implicit Arguments.

Lemma determiner_interpretation M G d (c : tm G ivty) rho sigma i :
  eval M (translate_determiner d c) rho sigma i = dvalue M d (eval M c rho sigma i) i.
Proof.
  destruct d; cbn [translate_determiner dvalue]; apply (function_extensionality M); intro P; cbn [eval]; apply truth_congr.
  - split; intros H x; specialize (H x); rewrite !eval_weaken in *; exact H.
  - split; intros [y H]; exists y; cbn [eval extend] in *;
      apply andb_true_iff in H; destruct H as [H1 H2]; apply andb_true_iff; split; auto;
      apply truth_spec; apply truth_spec in H1; intro x; specialize (H1 x);
      cbn [extend] in *; rewrite !eval_weaken in *; exact H1.
  - split; intros [x H]; exists x; rewrite !eval_weaken in *; exact H.
Qed.

Definition represents M G (r : pronouns G) rho sigma (s : pvalues M) :=
  forall n i, eval M (r n) rho sigma i = s n.
Arguments represents M {G} r rho sigma s.
Lemma shift_represents M G a (r : pronouns G) rho sigma (s : pvalues M) x :
  represents M r rho sigma s ->
  represents M (@shift G a r) (@extend M G a rho x) sigma s.
Proof. intros H n i; unfold shift; rewrite eval_weaken; apply H. Qed.
Lemma bind_represents M G (r : pronouns G) rho sigma (s : pvalues M) x n :
  represents M r rho sigma s ->
  represents M (bind r n) (@extend M G ic rho x) sigma (update s n x).
Proof.
  intros H m i; unfold bind, update; destruct (Nat.eqb m n); cbn; auto.
  rewrite eval_weaken; apply H.
Qed.

Theorem translation_interpretation M A (u : tree A) :
  forall G (r : pronouns G) rho sigma s,
  represents M r rho sigma s -> forall i,
  eval M (translate u r) rho sigma i = denote M u s i.
Proof.
  induction u; intros G r rho sigma values H i; cbn [translate denote].
  - reflexivity.
  - reflexivity.
  - cbn; apply (function_extensionality M); intro P; rewrite eval_weaken, H; reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite determiner_interpretation, IHu with (s := values); auto.
  - cbn; apply (function_extensionality M); intro x; rewrite eval_weaken.
    rewrite IHu1 with (s := values); auto.
    rewrite IHu2 with (s := update values n x); auto using bind_represents.
  - cbn; rewrite IHu1 with (s := values); auto.
    f_equal; apply (function_extensionality M); intro j; apply IHu2; auto.
  - cbn; rewrite IHu1 with (s := values); auto.
    f_equal; apply (function_extensionality M); intro j; apply IHu2; auto.
  - cbn; rewrite IHu1 with (s := values); auto.
    f_equal; apply (function_extensionality M); intro j; apply IHu2; auto.
  - cbn; rewrite IHu1 with (s := values); auto.
    f_equal; apply (function_extensionality M); intro j; apply IHu2; auto.
  - cbn; rewrite IHu1 with (s := values); auto.
    f_equal; apply (function_extensionality M); intro j; apply IHu2; auto.
  - cbn; rewrite IHu1 with (s := values); auto.
    f_equal; apply (function_extensionality M); intro j; apply IHu2; auto.
  - cbn; rewrite IHu1 with (s := values); auto.
    f_equal; apply (function_extensionality M); intro j; apply IHu2; auto.
  - destruct j; cbn; rewrite IHu1 with (s := values), IHu2 with (s := values); auto.
  - cbn; apply (function_extensionality M); intro x; destruct j; cbn;
      rewrite !eval_weaken, IHu1 with (s := values), IHu2 with (s := values); auto.
  - cbn; apply (function_extensionality M); intro P;
      rewrite !eval_weaken, IHu1 with (s := values), IHu2 with (s := values); auto.
  - cbn; rewrite IHu1 with (s := values); auto.
    f_equal; apply (function_extensionality M); intro j.
    apply (function_extensionality M); intro x; apply IHu2; apply bind_represents; auto.
  - cbn; apply (function_extensionality M); intro y.
    rewrite IHu1 with (s := values); auto using shift_represents.
    f_equal; apply (function_extensionality M); intro j.
    apply (function_extensionality M); intro x; cbn.
    rewrite IHu2 with (s := update values n x); auto using bind_represents, shift_represents.
  - cbn; apply (function_extensionality M); intro y.
    rewrite IHu1 with (s := values); auto using shift_represents.
    f_equal; apply (function_extensionality M); intro j.
    apply (function_extensionality M); intro x; cbn.
    rewrite IHu2 with (s := update values n x); auto using bind_represents, shift_represents.
  - assert (K : forall j, eval M (App (translate u1 r) (Up (translate u2 r))) rho sigma j =
        denote M u1 values j (fun k => denote M u2 values k)).
    { intro j; cbn; rewrite IHu1 with (s := values); auto.
      f_equal; apply (function_extensionality M); intro k; apply IHu2; auto. }
    cbn [eval] in K.
    match goal with k : tense_sign |- _ => destruct k end;
      cbn [sign svalue eval]; try (rewrite K; reflexivity);
      try apply (f_equal negb); apply truth_congr; split; intros [j [O Q]];
      exists j; split; auto; first [rewrite <- K; exact Q | rewrite K; exact Q].
Qed.

Corollary closed_translation_interpretation M A (u : tree A) sigma i :
  eval M (translate_closed u) (empty_env M) sigma i =
  denote M u (fun n => sigma ic (2 * n)) i.
Proof. apply translation_interpretation; intros n j; reflexivity. Qed.
