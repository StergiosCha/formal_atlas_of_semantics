(* PTQ pp. 23-25: variables u_(n,a), named binding and assignment update.
   This independent evaluator is connected to intrinsic syntax by a theorem.
   Eqdep_dec is used only for the proved UIP property of decidable ty equality;
   no general equality-proof axiom is imported. *)
From Coq Require Import List Bool Arith Logic.Eqdep_dec.
From MontaguePTQ Require Import Syntax Models.
Import ListNotations.
Set Implicit Arguments.

Definition named_env (F : ty -> Type) := forall a, nat -> F a.
Definition put {F} (r : named_env F) a n (x : F a) : named_env F :=
  fun b m => match ty_eq_dec a b with
  | left E => if Nat.eqb n m then eq_rect a F x b E else r b m
  | right _ => r b m
  end.
Lemma put_same F (r : named_env F) a n x : put r a n x a n = x.
Proof.
  unfold put; destruct (ty_eq_dec a a) as [E|N]; [|contradiction].
  rewrite Nat.eqb_refl; symmetry; apply eq_rect_eq_dec; exact ty_eq_dec.
Qed.
Lemma put_related F H (R : forall a, F a -> H a -> Prop)
  (r : named_env F) (s : named_env H) a n x y :
  (forall b m, R b (r b m) (s b m)) -> R a x y ->
  forall b m, R b (put r a n x b m) (put s a n y b m).
Proof.
  intros E V b m; unfold put; destruct (ty_eq_dec a b) as [K|N]; auto.
  destruct K; destruct (Nat.eqb n m); cbn; auto.
Qed.

Inductive ntm : ty -> Type :=
| NV : forall a, nat -> ntm a
| NC : forall a, nat -> ntm a
| NL : forall a b, nat -> ntm b -> ntm (arr a b)
| NA : forall a b, ntm (arr a b) -> ntm a -> ntm b
| NE : forall a, ntm a -> ntm a -> ntm t
| NN : ntm t -> ntm t
| NCj : ntm t -> ntm t -> ntm t
| NDj : ntm t -> ntm t -> ntm t
| NI : ntm t -> ntm t -> ntm t
| NB : ntm t -> ntm t -> ntm t
| NAll : forall a : ty, nat -> ntm t -> ntm t
| NEx : forall a : ty, nat -> ntm t -> ntm t
| NBox : ntm t -> ntm t
| NW : ntm t -> ntm t
| NH : ntm t -> ntm t
| NU : forall a, ntm a -> ntm (intens a)
| ND : forall a, ntm (intens a) -> ntm a.
Arguments NV a _ : clear implicits.
Arguments NC a _ : clear implicits.
Arguments NL a {b} _ _.
Arguments NA {a b} _ _.
Arguments NE {a} _ _.
Arguments NAll a _ _ : clear implicits.
Arguments NEx a _ _ : clear implicits.
Arguments NU {a} _.
Arguments ND {a} _.

Definition names G := named_env (tm G).
Definition nshift {G a} (r : names G) : names (a :: G) := fun b n => weaken (r b n).
Definition nbind {G a} (r : names G) n : names (a :: G) :=
  put (nshift r) a n (Var vz).
Fixpoint nameless {a} (p : ntm a) : forall G, names G -> tm G a :=
  match p in ntm a' return forall G, names G -> tm G a' with
  | NV a n => fun G r => r a n
  | NC a n => fun G _ => Con n
  | NL a n p => fun G r => Lam (nameless p (nbind r n))
  | NA p q => fun G r => App (nameless p r) (nameless q r)
  | NE p q => fun G r => Eq (nameless p r) (nameless q r)
  | NN p => fun G r => Neg (nameless p r)
  | NCj p q => fun G r => And (nameless p r) (nameless q r)
  | NDj p q => fun G r => Or (nameless p r) (nameless q r)
  | NI p q => fun G r => Imp (nameless p r) (nameless q r)
  | NB p q => fun G r => Iff (nameless p r) (nameless q r)
  | NAll a n p => fun G r => @All G a (nameless p (@nbind G a r n))
  | NEx a n p => fun G r => @Ex G a (nameless p (@nbind G a r n))
  | NBox p => fun G r => Box (nameless p r)
  | NW p => fun G r => Will (nameless p r)
  | NH p => fun G r => Has (nameless p r)
  | NU p => fun G r => Up (nameless p r)
  | ND p => fun G r => Down (nameless p r)
  end.
Definition initial_names : names [] := fun a n => Free n.
Definition embed_named {a} (p : ntm a) := nameless p initial_names.

Unset Implicit Arguments.
Fixpoint neval M {a} (p : ntm a) (r : free_env M) i : domain (carrier M) a :=
  match p in ntm a' return domain (carrier M) a' with
  | NV a n => r a n
  | NC a n => constants M a n i
  | NL a n p => fun x => neval M p (put r a n x) i
  | NA p q => neval M p r i (neval M q r i)
  | NE p q => truth (boolean_truth M) (neval M p r i = neval M q r i)
  | NN p => negb (neval M p r i)
  | NCj p q => andb (neval M p r i) (neval M q r i)
  | NDj p q => orb (neval M p r i) (neval M q r i)
  | NI p q => orb (negb (neval M p r i)) (neval M q r i)
  | NB p q => Bool.eqb (neval M p r i) (neval M q r i)
  | NAll a n p => truth (boolean_truth M) (forall x, neval M p (put r a n x) i = true)
  | NEx a n p => truth (boolean_truth M) (exists x, neval M p (put r a n x) i = true)
  | NBox p => truth (boolean_truth M) (forall j, neval M p r j = true)
  | NW p => truth (boolean_truth M) (exists j,
      before (carrier M) (snd i) j /\ neval M p r (fst i,j) = true)
  | NH p => truth (boolean_truth M) (exists j,
      before (carrier M) j (snd i) /\ neval M p r (fst i,j) = true)
  | NU p => fun j => neval M p r j
  | ND p => neval M p r i i
  end.
Set Implicit Arguments.

Definition names_match M G (r : names G) rho sigma (s : free_env M) :=
  forall a n i, eval M (r a n) rho sigma i = s a n.
Arguments names_match M {G} r rho sigma s.
Lemma nbind_matches M G a (r : names G) rho sigma s n x :
  names_match M r rho sigma s ->
  names_match M (@nbind G a r n) (@extend M G a rho x) sigma (put s a n x).
Proof.
  intros H b m i; unfold nbind.
  apply (@put_related (tm (a :: G)) (domain (carrier M))
    (fun b (p : tm (a :: G) b) y => eval M p (@extend M G a rho x) sigma i = y)
    (@nshift G a r) s a n (Var vz) x);
    [intros c k; unfold nshift; rewrite eval_weaken; apply H | reflexivity].
Qed.

Theorem named_interpretation M a (p : ntm a) : forall G (r : names G) rho sigma s,
  names_match M r rho sigma s -> forall i,
  eval M (nameless p r) rho sigma i = neval M p s i.
Proof.
  induction p; intros G r rho sigma s H i; cbn;
    try reflexivity; try apply H;
    try (rewrite IHp1 with (s := s), IHp2 with (s := s); auto; fail);
    try (rewrite IHp with (s := s); auto; fail).
  - apply (function_extensionality M); intro x; apply IHp; apply nbind_matches; auto.
  - apply truth_congr; split; intros Q x;
      [rewrite <- IHp with (r := nbind r n) (rho := extend rho x) (sigma := sigma)
      | rewrite IHp with (s := put s a n x)]; auto using nbind_matches.
  - apply truth_congr; split; intros [x Q]; exists x;
      [rewrite <- IHp with (r := nbind r n) (rho := extend rho x) (sigma := sigma)
      | rewrite IHp with (s := put s a n x)]; auto using nbind_matches.
  - apply truth_congr; split; intros Q j;
      [rewrite <- IHp with (r := r) (rho := rho) (sigma := sigma)
      | rewrite IHp with (s := s)]; auto.
  - apply truth_congr; split; intros [j [O Q]]; exists j; split; auto;
      [rewrite <- IHp with (r := r) (rho := rho) (sigma := sigma)
      | rewrite IHp with (s := s)]; auto.
  - apply truth_congr; split; intros [j [O Q]]; exists j; split; auto;
      [rewrite <- IHp with (r := r) (rho := rho) (sigma := sigma)
      | rewrite IHp with (s := s)]; auto.
  - apply (function_extensionality M); intro j; apply IHp; auto.
Qed.

Corollary embed_named_interpretation M a (p : ntm a) sigma i :
  eval M (embed_named p) (empty_env M) sigma i = neval M p sigma i.
Proof. apply named_interpretation; intros b n j; reflexivity. Qed.

Example named_shadowing_is_local :
  embed_named (NL e 0 (NL e 0 (NV e 0))) = @Lam [] e (arr e e) (Lam (Var vz)).
Proof. reflexivity. Qed.
Example distinct_types_do_not_shadow :
  embed_named (NL e 0 (NL t 0 (NV e 0))) = @Lam [] e (arr t e) (Lam (Var (vs vz))).
Proof. reflexivity. Qed.
Example unrelated_free_names_survive :
  embed_named (NL e 0 (NV e 1)) = @Lam [] e e (Free 1).
Proof. reflexivity. Qed.
