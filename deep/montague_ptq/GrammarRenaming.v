(* Capture-safe injective renaming of the complete PTQ grammar.
   Both meanings and token realization commute with renaming. *)
From Coq Require Import List Bool Arith Strings.String.
From MontaguePTQ Require Import Syntax Models Grammar Meaning Surface PronounSupport SurfaceAmendment.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Fixpoint rename_tree f {A} (u : tree A) : tree A := match u with
  | s1_word w => s1_word w | s1_name n => s1_name n
  | s1_pronoun n => s1_pronoun (f n) | s1_be => s1_be
  | s1_necessarily => s1_necessarily
  | s2 d c => s2 d (rename_tree f c)
  | s3 c n p => s3 (rename_tree f c) (f n) (rename_tree f p)
  | s4 p q => s4 (rename_tree f p) (rename_tree f q)
  | s5 p q => s5 (rename_tree f p) (rename_tree f q)
  | s6 p q => s6 (rename_tree f p) (rename_tree f q)
  | s7 p q => s7 (rename_tree f p) (rename_tree f q)
  | s8 p q => s8 (rename_tree f p) (rename_tree f q)
  | s9 p q => s9 (rename_tree f p) (rename_tree f q)
  | s10 p q => s10 (rename_tree f p) (rename_tree f q)
  | s11 j p q => s11 j (rename_tree f p) (rename_tree f q)
  | s12 j p q => s12 j (rename_tree f p) (rename_tree f q)
  | s13 p q => s13 (rename_tree f p) (rename_tree f q)
  | s14 p n q => s14 (rename_tree f p) (f n) (rename_tree f q)
  | s15 p n q => s15 (rename_tree f p) (f n) (rename_tree f q)
  | s16 p n q => s16 (rename_tree f p) (f n) (rename_tree f q)
  | s17 k p q => s17 k (rename_tree f p) (rename_tree f q)
  end.
Definition injective_name_map (f : nat -> nat) := forall n m, f n = f m -> n = m.

Lemma injective_eqb f (F : injective_name_map f) n m :
  Nat.eqb (f n) (f m) = Nat.eqb n m.
Proof.
  destruct (Nat.eqb (f n) (f m)) eqn:H, (Nat.eqb n m) eqn:K; try reflexivity;
    apply Nat.eqb_eq in H || apply Nat.eqb_neq in H;
    apply Nat.eqb_eq in K || apply Nat.eqb_neq in K; congruence || (exfalso; apply K; apply F; exact H).
Qed.

Lemma pullback_update M f (F : injective_name_map f) (r : pvalues M) n x :
  (fun m => update r (f n) x (f m)) = update (fun m => r (f m)) n x.
Proof.
  apply (function_extensionality M); intro m; unfold update; rewrite (injective_eqb F); reflexivity.
Qed.

Theorem rename_tree_interpretation M f (F : injective_name_map f) A (u : tree A) :
  forall r i, denote M (rename_tree f u) r i = denote M u (fun n => r (f n)) i.
Proof.
  induction u; intros r i; cbn [rename_tree denote]; try reflexivity.
  - rewrite IHu; reflexivity.
  - apply (function_extensionality M); intro x; rewrite IHu1, IHu2, (pullback_update F); reflexivity.
  - rewrite IHu1; f_equal; apply (function_extensionality M); intro j; apply IHu2.
  - rewrite IHu1; f_equal; apply (function_extensionality M); intro j; apply IHu2.
  - rewrite IHu1; f_equal; apply (function_extensionality M); intro j; apply IHu2.
  - rewrite IHu1; f_equal; apply (function_extensionality M); intro j; apply IHu2.
  - rewrite IHu1; f_equal; apply (function_extensionality M); intro j; apply IHu2.
  - rewrite IHu1; f_equal; apply (function_extensionality M); intro j; apply IHu2.
  - rewrite IHu1; f_equal; apply (function_extensionality M); intro j; apply IHu2.
  - rewrite IHu1, IHu2; reflexivity.
  - apply (function_extensionality M); intro x; rewrite IHu1, IHu2; reflexivity.
  - apply (function_extensionality M); intro p; rewrite IHu1, IHu2; reflexivity.
  - rewrite IHu1; f_equal; apply (function_extensionality M); intro j;
      apply (function_extensionality M); intro x; rewrite IHu2, (pullback_update F); reflexivity.
  - apply (function_extensionality M); intro y; rewrite IHu1; f_equal;
      apply (function_extensionality M); intro j; apply (function_extensionality M); intro x;
      rewrite IHu2, (pullback_update F); reflexivity.
  - apply (function_extensionality M); intro y; rewrite IHu1; f_equal;
      apply (function_extensionality M); intro j; apply (function_extensionality M); intro x;
      rewrite IHu2, (pullback_update F); reflexivity.
  - f_equal; apply (function_extensionality M); intro j; rewrite IHu1; f_equal;
      apply (function_extensionality M); intro k; apply IHu2.
Qed.

Definition rename_token f u := match u with indexed n c => indexed (f n) c | _ => u end.
Definition rename_tokens f := map (rename_token f).
Definition rename_result f := option_map (rename_tokens f).

Lemma rename_tokens_append f xs ys : rename_tokens f (xs ++ ys) =
  (rename_tokens f xs ++ rename_tokens f ys)%list.
Proof. apply map_app. Qed.
Lemma rename_tokens_gender f xs : first_gender (rename_tokens f xs) = first_gender xs.
Proof. induction xs as [|u xs IH]; [reflexivity|]; destruct u; cbn; auto. Qed.
Lemma rename_tokens_bare f xs : bare_pronoun (rename_tokens f xs) = option_map f (bare_pronoun xs).
Proof. destruct xs as [|u xs]; [reflexivity|]; destruct u; destruct xs; cbn; try reflexivity; destruct c; reflexivity. Qed.
Lemma rename_tokens_object f xs : rename_tokens f (object_form xs) = object_form (rename_tokens f xs).
Proof. destruct xs as [|u xs]; [reflexivity|]; destruct u; destruct xs; cbn; try reflexivity; destruct c; reflexivity. Qed.

Lemma rename_tokens_replace f (F : injective_name_map f) n g xs :
  rename_tokens f (map (replace_pronoun n g) xs) =
  map (replace_pronoun (f n) g) (rename_tokens f xs).
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; cbn [rename_tokens map]; rewrite IH;
    f_equal; destruct u; cbn [rename_token replace_pronoun]; try reflexivity;
    rewrite (injective_eqb F); destruct (Nat.eqb n n0); reflexivity.
Qed.
Lemma rename_tokens_rename f (F : injective_name_map f) n k xs :
  rename_tokens f (map (rename_pronoun n k) xs) =
  map (rename_pronoun (f n) (f k)) (rename_tokens f xs).
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; cbn [rename_tokens map]; rewrite IH;
    f_equal; destruct u; cbn [rename_token rename_pronoun]; try reflexivity;
    rewrite (injective_eqb F); destruct (Nat.eqb n n0); reflexivity.
Qed.
Lemma rename_tokens_insert f (F : injective_name_map f) n alpha g xs :
  rename_result f (insert_first n alpha g xs) =
  insert_first (f n) (rename_tokens f alpha) g (rename_tokens f xs).
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; destruct u;
    cbn [insert_first rename_tokens map rename_token];
    try (rewrite <- IH; destruct (insert_first n alpha g xs); reflexivity).
  rewrite (injective_eqb F); destruct (Nat.eqb n n0).
  - cbn [rename_result option_map]; rewrite rename_tokens_append, (rename_tokens_replace F); reflexivity.
  - rewrite <- IH; destruct (insert_first n alpha g xs); reflexivity.
Qed.
Lemma rename_tokens_f10 f (F : injective_name_map f) n alpha xs :
  rename_result f (f10 n alpha xs) = f10 (f n) (rename_tokens f alpha) (rename_tokens f xs).
Proof.
  unfold f10; rewrite rename_tokens_bare, rename_tokens_gender.
  destruct (bare_pronoun alpha); cbn [option_map].
  - cbn [rename_result option_map]; rewrite (rename_tokens_rename F); reflexivity.
  - destruct (first_gender alpha); [apply rename_tokens_insert; exact F|reflexivity].
Qed.
Lemma rename_tokens_inflect f form xs :
  rename_result f (inflect_first form xs) = inflect_first form (rename_tokens f xs).
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; destruct u;
    cbn [inflect_first rename_tokens map rename_token];
    try (rewrite <- IH; destruct (inflect_first form xs); reflexivity).
  reflexivity.
Qed.
Lemma rename_result_combine f op op' :
  (forall xs ys, rename_result f (op xs ys) = op' (rename_tokens f xs) (rename_tokens f ys)) ->
  forall a b, rename_result f (combine op a b) = combine op' (rename_result f a) (rename_result f b).
Proof. intros H [xs|] [ys|]; try reflexivity; apply H. Qed.
Lemma rename_result_concat f a b : rename_result f (combine concat_tokens a b) =
  combine concat_tokens (rename_result f a) (rename_result f b).
Proof. apply rename_result_combine; intros; cbn [concat_tokens rename_result option_map]; rewrite rename_tokens_append; reflexivity. Qed.
Lemma rename_result_object f a b : rename_result f (combine (fun x y => concat_tokens x (object_form y)) a b) =
  combine (fun x y => concat_tokens x (object_form y)) (rename_result f a) (rename_result f b).
Proof. apply rename_result_combine; intros; cbn [concat_tokens rename_result option_map]; rewrite rename_tokens_append, rename_tokens_object; reflexivity. Qed.
Lemma rename_result_join f j a b : rename_result f (combine (join_tokens j) a b) =
  combine (join_tokens j) (rename_result f a) (rename_result f b).
Proof. apply rename_result_combine; intros; cbn [join_tokens rename_result option_map]; repeat rewrite rename_tokens_append; reflexivity. Qed.
Lemma rename_result_subject f form a b : rename_result f (combine (subject_verb form) a b) =
  combine (subject_verb form) (rename_result f a) (rename_result f b).
Proof.
  apply rename_result_combine; intros; unfold subject_verb; rewrite <- rename_tokens_inflect;
    destruct (inflect_first form ys); cbn [rename_result option_map]; [rewrite rename_tokens_append|]; reflexivity.
Qed.

Theorem rename_tree_surface f (F : injective_name_map f) A (u : tree A) :
  realize (rename_tree f u) = rename_result f (realize u).
Proof.
  induction u; cbn [rename_tree realize]; try reflexivity.
  - destruct l; reflexivity.
  - rewrite IHu; destruct (realize u); reflexivity.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_combine; intros;
      rewrite rename_tokens_gender; destruct (first_gender xs); [|reflexivity];
      cbn [rename_result option_map]; repeat rewrite rename_tokens_append;
      rewrite (rename_tokens_replace F); reflexivity.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_subject.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_object.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_object.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_concat.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_concat.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_concat.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_combine; intros;
      cbn [concat_tokens rename_result option_map]; rewrite rename_tokens_append; reflexivity.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_join.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_join.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_join.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_combine; apply rename_tokens_f10; exact F.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_combine; apply rename_tokens_f10; exact F.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_combine; apply rename_tokens_f10; exact F.
  - rewrite IHu1, IHu2; symmetry; apply rename_result_subject.
Qed.

Lemma rename_result_first f xs : rename_result f (first_present xs) = first_present (rename_result f xs).
Proof. destruct xs; [apply rename_tokens_inflect|reflexivity]. Qed.
Definition rename_plan f p := {| plain_tokens := rename_result f (plain_tokens p);
  present_tokens := rename_result f (present_tokens p) |}.
Lemma rename_ordinary_plan f xs : rename_plan f (ordinary_plan xs) = ordinary_plan (rename_result f xs).
Proof. unfold rename_plan, ordinary_plan; cbn; rewrite rename_result_first; reflexivity. Qed.
Lemma rename_coordinated_plan f policy xs ys :
  rename_plan f (coordinated_plan policy xs ys) =
  coordinated_plan policy (rename_result f xs) (rename_result f ys).
Proof. destruct policy; unfold rename_plan, coordinated_plan; cbn; try rewrite rename_result_first; reflexivity. Qed.
Lemma rename_result_reverse f a b : rename_result f (combine (fun x y => concat_tokens y x) a b) =
  combine (fun x y => concat_tokens y x) (rename_result f a) (rename_result f b).
Proof. apply rename_result_combine; intros; cbn [concat_tokens rename_result option_map]; rewrite rename_tokens_append; reflexivity. Qed.
Lemma rename_result_f10 f (F : injective_name_map f) n a b :
  rename_result f (combine (f10 n) a b) = combine (f10 (f n)) (rename_result f a) (rename_result f b).
Proof. apply rename_result_combine; apply rename_tokens_f10; exact F. Qed.
Lemma rename_result_determiner f d a :
  rename_result f (match a with Some cs => Some (literal
    (match d with every => "every" | the => "the" | a_or_an => "a" end) :: cs)
    | None => None end) =
  match rename_result f a with Some cs => Some (literal
    (match d with every => "every" | the => "the" | a_or_an => "a" end) :: cs)
    | None => None end.
Proof. destruct a; reflexivity. Qed.
Lemma rename_result_relative f (F : injective_name_map f) n a b :
  rename_result f (combine (fun cs ps => match first_gender cs with
    | Some g => Some (cs ++ [literal "such"; literal "that"] ++ map (replace_pronoun n g) ps)%list
    | None => None end) a b) =
  combine (fun cs ps => match first_gender cs with
    | Some g => Some (cs ++ [literal "such"; literal "that"] ++ map (replace_pronoun (f n) g) ps)%list
    | None => None end) (rename_result f a) (rename_result f b).
Proof.
  apply rename_result_combine; intros; rewrite rename_tokens_gender;
    destruct (first_gender xs); [|reflexivity]; cbn [rename_result option_map];
    repeat rewrite rename_tokens_append; rewrite (rename_tokens_replace F); reflexivity.
Qed.

Theorem rename_tree_plan_components f (F : injective_name_map f) policy A (u : tree A) :
  plain_tokens (plan policy (rename_tree f u)) = rename_result f (plain_tokens (plan policy u)) /\
  present_tokens (plan policy (rename_tree f u)) = rename_result f (present_tokens (plan policy u)).
Proof.
  induction u; cbn [rename_tree plan ordinary_plan coordinated_plan plain_tokens present_tokens];
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with H : ?x = ?y |- _ => rewrite H end;
    destruct policy; repeat rewrite rename_result_first;
    repeat rewrite rename_result_determiner; repeat rewrite (rename_result_relative F);
    repeat rewrite rename_result_concat; repeat rewrite rename_result_object;
    repeat rewrite rename_result_reverse; repeat rewrite rename_result_join;
    repeat rewrite (rename_result_f10 F); repeat rewrite rename_result_subject;
    try (split; reflexivity).
  all: destruct l; split; reflexivity.
Qed.

Theorem rename_tree_plan f (F : injective_name_map f) policy A (u : tree A) :
  plan policy (rename_tree f u) = rename_plan f (plan policy u).
Proof.
  pose proof (@rename_tree_plan_components f F policy A u) as [H K].
  destruct (plan policy (rename_tree f u)), (plan policy u); cbn in H, K;
    unfold rename_plan; cbn; subst; reflexivity.
Qed.

Corollary rename_tree_amended_surface f (F : injective_name_map f) A (u : tree A) :
  amended_tokens (rename_tree f u) = rename_result f (amended_tokens u).
Proof. unfold amended_tokens; rewrite (rename_tree_plan F); reflexivity. Qed.
