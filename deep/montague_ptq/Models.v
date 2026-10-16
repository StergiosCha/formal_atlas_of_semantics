(* PTQ pp. 24-25 and editorial notes 9-10, p. 33.
   Boolean truth, inhabited carriers, linear time, index-dependent constants.
   Full function spaces are internal to Coq; classical Boolean reflection
   and function extensionality are explicit model obligations, not axioms. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax.
Import ListNotations.
Set Implicit Arguments.

Definition FunExt := forall (A B : Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.
Definition ClassicalDecision := forall P : Prop, {P} + {~ P}.
Record BooleanTruth := {
  truth : Prop -> bool;
  truth_spec : forall P, truth P = true <-> P
}.
Arguments truth _ _.

Definition decision_truth (CD : ClassicalDecision) : BooleanTruth.
Proof.
  refine {| truth := fun P => if CD P then true else false |}.
  intro P; destruct (CD P); split; intro H; auto; discriminate.
Defined.

Theorem reflection_requires_classical_truth (B : BooleanTruth) (P : Prop) : P \/ ~ P.
Proof.
  destruct (truth B P) eqn:H.
  - left; apply (proj1 (truth_spec B P)); exact H.
  - right; intro HP; apply (proj2 (truth_spec B P)) in HP; congruence.
Qed.

Lemma truth_congr (B : BooleanTruth) (P Q : Prop) :
  (P <-> Q) -> truth B P = truth B Q.
Proof.
  intro H; destruct (truth B P) eqn:HP, (truth B Q) eqn:HQ; auto.
  - apply (proj1 (truth_spec B P)) in HP.
    apply H in HP; apply (proj2 (truth_spec B Q)) in HP; congruence.
  - apply (proj1 (truth_spec B Q)) in HQ.
    apply H in HQ; apply (proj2 (truth_spec B P)) in HQ; congruence.
Qed.

Record frame := {
  entity : Type; world : Type; time : Type;
  entity_nonempty : inhabited entity;
  world_nonempty : inhabited world;
  time_nonempty : inhabited time;
  time_le : time -> time -> Prop;
  time_refl : forall x, time_le x x;
  time_trans : forall x y z, time_le x y -> time_le y z -> time_le x z;
  time_antisym : forall x y, time_le x y -> time_le y x -> x = y;
  time_total : forall x y, time_le x y \/ time_le y x
}.
Definition index (F : frame) := (world F * time F)%type.
Definition before (F : frame) (x y : time F) := time_le F x y /\ x <> y.
Fixpoint domain (F : frame) (a : ty) : Type :=
  match a with
  | e => entity F | t => bool
  | arr a b => domain F a -> domain F b
  | intens a => index F -> domain F a
  end.
Record model := {
  carrier : frame;
  boolean_truth : BooleanTruth;
  function_extensionality : FunExt;
  constants : forall a, nat -> index carrier -> domain carrier a
}.

Definition free_env (M : model) := forall a, nat -> domain (carrier M) a.
Definition env (M : model) G := forall a, var G a -> domain (carrier M) a.
Definition extend {M G a} (rho : env M G) (x : domain (carrier M) a) : env M (a :: G) :=
  fun b v => match v in var G' b' return
    match G' with
    | nil => unit
    | c :: G0 => env M G0 -> domain (carrier M) c -> domain (carrier M) b'
    end with
  | @vz _ _ => fun _ x0 => x0
  | @vs _ _ _ w => fun r _ => r _ w
  end rho x.
Definition empty_env M : env M [] := fun a v =>
  match v in var G b return match G with [] => domain (carrier M) b | _ => unit end with
  | vz => tt | vs _ => tt
  end.

Unset Implicit Arguments.
Fixpoint eval (M : model) {G a} (u : tm G a) (rho : env M G)
  (sigma : free_env M) (i : index (carrier M)) : domain (carrier M) a :=
  match u in tm G' a' return env M G' -> domain (carrier M) a' with
  | Var v => fun r => r _ v
  | Free n => fun _ => sigma _ n
  | Con n => fun _ => constants M _ n i
  | Lam p => fun r x => eval M p (extend r x) sigma i
  | App p q => fun r => eval M p r sigma i (eval M q r sigma i)
  | Eq p q => fun r => truth (boolean_truth M) (eval M p r sigma i = eval M q r sigma i)
  | Neg p => fun r => negb (eval M p r sigma i)
  | And p q => fun r => andb (eval M p r sigma i) (eval M q r sigma i)
  | Or p q => fun r => orb (eval M p r sigma i) (eval M q r sigma i)
  | Imp p q => fun r => orb (negb (eval M p r sigma i)) (eval M q r sigma i)
  | Iff p q => fun r => Bool.eqb (eval M p r sigma i) (eval M q r sigma i)
  | All p => fun r => truth (boolean_truth M) (forall x, eval M p (extend r x) sigma i = true)
  | Ex p => fun r => truth (boolean_truth M) (exists x, eval M p (extend r x) sigma i = true)
  | Box p => fun r => truth (boolean_truth M) (forall j, eval M p r sigma j = true)
  | Will p => fun r => truth (boolean_truth M) (exists j,
      before (carrier M) (snd i) j /\ eval M p r sigma (fst i, j) = true)
  | Has p => fun r => truth (boolean_truth M) (exists j,
      before (carrier M) j (snd i) /\ eval M p r sigma (fst i, j) = true)
  | Up p => fun r j => eval M p r sigma j
  | Down p => fun r => eval M p r sigma i i
  end rho.
Set Implicit Arguments.

Theorem necessity_clause M G (p : tm G t) rho sigma i :
  eval M (Box p) rho sigma i = true <->
  forall w j, eval M p rho sigma (w,j) = true.
Proof.
  cbn; rewrite truth_spec. split; intros H; [intros w j; apply H | intros [w j]; apply H].
Qed.
Theorem future_clause M G (p : tm G t) rho sigma w j :
  eval M (Will p) rho sigma (w,j) = true <->
  exists j', time_le (carrier M) j j' /\ j <> j' /\ eval M p rho sigma (w,j') = true.
Proof. cbn; rewrite truth_spec; unfold before; firstorder. Qed.
Theorem past_clause M G (p : tm G t) rho sigma w j :
  eval M (Has p) rho sigma (w,j) = true <->
  exists j', time_le (carrier M) j' j /\ j' <> j /\ eval M p rho sigma (w,j') = true.
Proof. cbn; rewrite truth_spec; unfold before; firstorder. Qed.
Theorem down_up M G a (p : tm G a) rho sigma i :
  eval M (Down (Up p)) rho sigma i = eval M p rho sigma i.
Proof. reflexivity. Qed.
Theorem constant_clause M G a n (rho : env M G) sigma i :
  eval M (@Con G a n) rho sigma i = constants M a n i.
Proof. reflexivity. Qed.
Theorem equality_clause M G a (p q : tm G a) rho sigma i :
  eval M (Eq p q) rho sigma i = true <-> eval M p rho sigma i = eval M q rho sigma i.
Proof. apply truth_spec. Qed.

Theorem eval_rename M G a (p : tm G a) : forall D (r : ren G D)
  (rho : env M G) (tau : env M D) sigma,
  (forall b v, tau _ (r b v) = rho b v) ->
  forall i, eval M (rename p r) tau sigma i = eval M p rho sigma i.
Proof.
  induction p; intros D r rho tau sigma H i; cbn;
    try reflexivity; try (apply H);
    try (rewrite IHp1 with (rho := rho), IHp2 with (rho := rho); auto; fail);
    try (rewrite IHp with (rho := rho); auto; fail).
  - apply (function_extensionality M); intro x; apply IHp.
    apply var_cases; cbn; auto.
  - apply truth_congr. assert (K : forall x j,
      eval M (rename p (lift_ren r)) (extend tau x) sigma j =
      eval M p (extend rho x) sigma j).
    { intros; apply IHp; apply var_cases; cbn; auto. }
    split; intros Q x; [rewrite <- K | rewrite K]; apply Q.
  - apply truth_congr. assert (K : forall x j,
      eval M (rename p (lift_ren r)) (extend tau x) sigma j =
      eval M p (extend rho x) sigma j).
    { intros; apply IHp; apply var_cases; cbn; auto. }
    split; intros [x Q]; exists x; [rewrite <- K | rewrite K]; exact Q.
  - apply truth_congr; split; intros Q j;
      [rewrite <- IHp with (tau := tau) (r := r) | rewrite IHp with (rho := rho)]; auto.
  - apply truth_congr; split; intros [j [Hj Q]]; exists j; split; auto;
      [rewrite <- IHp with (tau := tau) (r := r) | rewrite IHp with (rho := rho)]; auto.
  - apply truth_congr; split; intros [j [Hj Q]]; exists j; split; auto;
      [rewrite <- IHp with (tau := tau) (r := r) | rewrite IHp with (rho := rho)]; auto.
  - apply (function_extensionality M); intro j; apply IHp; auto.
Qed.

Corollary eval_weaken M G a b (p : tm G b) rho sigma x i :
  eval M (@weaken G a b p) (extend rho x) sigma i = eval M p rho sigma i.
Proof. apply eval_rename; intros; reflexivity. Qed.
