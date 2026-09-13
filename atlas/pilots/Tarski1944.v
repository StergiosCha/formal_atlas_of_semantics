(* Prospective P2 pilot, paper 1. Tarski 1944 sections 4,9,11;
   printed pp.343-345,350-353. Object syntax is distinct from its Coq
   metalanguage interpretation. Recursive satisfaction precedes truth.
   This is a particular first-order language, not a definition of truth
   for Coq or unrestricted natural language. No internal truth predicate,
   diagonal lemma, classical bivalence, or undefinability theorem claimed.
   Domain has a named snow object; the fragment is constructive. *)
Require Import Arith.

Inductive term := var (x : nat) | snow.
Inductive formula := atom (p : nat) (t : term)
                   | both (a b : formula) | neg (a : formula)
                   | all (x : nat) (a : formula).
Definition occurs x t := match t with var y => x = y | snow => False end.
Fixpoint free x f : Prop :=
  match f with
  | atom _ t => occurs x t
  | both a b => free x a \/ free x b
  | neg a => free x a
  | all y a => x <> y /\ free x a
  end.
Definition closed f := forall x, ~ free x f.

Section Interpretation.
Variable D : Type.
Variable snow_object : D.
Variable predicates : nat -> D -> Prop.
Definition update (rho : nat -> D) x d :=
  fun y => if Nat.eq_dec y x then d else rho y.
Definition denote_term (rho : nat -> D) t :=
  match t with var x => rho x | snow => snow_object end.
Fixpoint satisfies (rho : nat -> D) f : Prop :=
  match f with
  | atom p t => predicates p (denote_term rho t)
  | both a b => satisfies rho a /\ satisfies rho b
  | neg a => ~ satisfies rho a
  | all x a => forall d, satisfies (update rho x d) a
  end.
Definition truth f := forall rho, satisfies rho f.

Theorem satisfaction_depends_on_free_variables : forall f rho sigma,
  (forall x, free x f -> rho x = sigma x) ->
  (satisfies rho f <-> satisfies sigma f).
Proof.
  induction f as [p t|a IHa b IHb|a IH|x a IH]; intros rho sigma H; simpl in *.
  - destruct t as [x|]; simpl in *.
    + rewrite (H x eq_refl); reflexivity.
    + reflexivity.
  - rewrite (IHa rho sigma), (IHb rho sigma); try tauto.
    + intros y Hy; apply H; auto.
    + intros y Hy; apply H; auto.
  - rewrite (IH rho sigma H); reflexivity.
  - assert (E : forall d, satisfies (update rho x d) a <->
                         satisfies (update sigma x d) a).
    { intros d; apply IH; intros y Hy; unfold update.
      destruct (Nat.eq_dec y x); [reflexivity | apply H; auto]. }
    split; intros Hall d; [apply (proj1 (E d)) | apply (proj2 (E d))]; apply Hall.
Qed.

Theorem closed_assignment_invariance : forall f rho sigma,
  closed f -> (satisfies rho f <-> satisfies sigma f).
Proof.
  intros f rho sigma H; apply satisfaction_depends_on_free_variables.
  intros x Hx; exfalso; exact (H x Hx).
Qed.

(* Language-specific T-equivalences follow from satisfaction invariance;
   the schema itself is not substituted for a recursive definition. *)
Theorem closed_truth_instance : forall f rho,
  closed f -> (truth f <-> satisfies rho f).
Proof.
  intros f rho H; split.
  - intros Ht; apply Ht.
  - intros Hr sigma; apply (proj1 (closed_assignment_invariance f rho sigma H)); exact Hr.
Qed.

Theorem snow_instance : truth (atom 0 snow) <-> predicates 0 snow_object.
Proof.
  split; [intros H; exact (H (fun _ => snow_object)) | intros H rho; exact H].
Qed.

Theorem contradiction_has_no_satisfying_assignment : forall f rho,
  ~ satisfies rho (both f (neg f)).
Proof. intros f rho [H Hnot]; exact (Hnot H). Qed.

Theorem no_true_contradiction : forall f, ~ truth (both f (neg f)).
Proof.
  intros f H; exact (contradiction_has_no_satisfying_assignment f
    (fun _ => snow_object) (H (fun _ => snow_object))).
Qed.
End Interpretation.

Theorem universal_closes_variable : closed (all 0 (atom 0 (var 0))).
Proof. intros x [Hne Heq]; apply Hne; exact Heq. Qed.
