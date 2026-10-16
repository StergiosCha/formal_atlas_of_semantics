(* Extensional C workbench, v0. Source: Chatzikyriakidis and Luo (2020),
   section 1.3.1 and Appendix A1, following Luo and Soloviev (2017).
   Typed de Bruijn syntax separates object formulas from their derivations.
   No worlds, choice, eta, extensional equality or Henkin completeness claimed. *)
From Coq Require Import List.
Import ListNotations.
Set Implicit Arguments.

Inductive ty : Type := entity | truth | arrow (a b : ty).

Inductive var : list ty -> ty -> Type :=
| vz : forall G a, var (a :: G) a
| vs : forall G a b, var G a -> var (b :: G) a.
Arguments vz {G a}.
Arguments vs {G a b} _.

(* Indexed case analysis without the equality axiom that Program.Equality's
   dependent destruction can introduce. *)
Lemma var_cons_cases G a (P : forall b, var (a :: G) b -> Prop) :
  P a vz -> (forall b (v : var G b), P b (vs v)) -> forall b v, P b v.
Proof.
  intros Hz Hs b v; revert P Hz Hs.
  exact (match v as w in var D c return
    match D as D0 return var D0 c -> Prop with
    | nil => fun _ => True
    | d :: D0 => fun w0 => forall P : forall b, var (d :: D0) b -> Prop,
        P d vz -> (forall b v, P b (vs v)) -> P c w0
    end w with
  | @vz _ _ => fun P Hz _ => Hz
  | @vs _ _ _ w0 => fun P _ Hs => Hs _ w0
  end).
Qed.

Section Language.
Variable symbol : ty -> Type.

Inductive tm : list ty -> ty -> Type :=
| Var : forall G a, var G a -> tm G a
| Const : forall G a, symbol a -> tm G a
| Lam : forall G a b, tm (a :: G) b -> tm G (arrow a b)
| App : forall G a b, tm G (arrow a b) -> tm G a -> tm G b
| Imp : forall G, tm G truth -> tm G truth -> tm G truth
| All : forall G a, tm (a :: G) truth -> tm G truth.
Arguments Var {G a} _.
Arguments Const {G a} _.
Arguments Lam {G a b} _.
Arguments App {G a b} _ _.
Arguments Imp {G} _ _.
Arguments All {G a} _.

Definition ren G D := forall a, var G a -> var D a.

Definition lift_ren {G D a} (r : ren G D) : ren (a :: G) (a :: D) :=
  fun b v => match v in var G' b' return
    match G' with
    | nil => unit
    | c :: G0 => (ren G0 D -> var (c :: D) b')
    end with
  | @vz _ _ => fun _ => vz
  | @vs _ _ _ w => fun r0 => vs (r0 _ w)
  end r.

Fixpoint rename {G a} (t : tm G a) : forall D, ren G D -> tm D a :=
  match t in tm G' a' return forall D, ren G' D -> tm D a' with
  | Var v => fun D r => Var (r _ v)
  | Const c => fun D _ => Const c
  | Lam u => fun D r => Lam (rename u (lift_ren r))
  | App f x => fun D r => App (rename f r) (rename x r)
  | Imp p q => fun D r => Imp (rename p r) (rename q r)
  | All p => fun D r => All (rename p (lift_ren r))
  end.

Definition weaken {G a b} (t : tm G b) : tm (a :: G) b :=
  rename t (fun _ v => vs v).

Definition sub G D := forall a, var G a -> tm D a.

Definition lift_sub {G D a} (s : sub G D) : sub (a :: G) (a :: D) :=
  fun b v => match v in var G' b' return
    match G' with
    | nil => unit
    | c :: G0 => (sub G0 D -> tm (c :: D) b')
    end with
  | @vz _ _ => fun _ => Var vz
  | @vs _ _ _ w => fun s0 => weaken (s0 _ w)
  end s.

Fixpoint subst {G a} (t : tm G a) : forall D, sub G D -> tm D a :=
  match t in tm G' a' return forall D, sub G' D -> tm D a' with
  | Var v => fun D s => s _ v
  | Const c => fun D _ => Const c
  | Lam u => fun D s => Lam (subst u (lift_sub s))
  | App f x => fun D s => App (subst f s) (subst x s)
  | Imp p q => fun D s => Imp (subst p s) (subst q s)
  | All p => fun D s => All (subst p (lift_sub s))
  end.

Definition head_sub {G a} (u : tm G a) : sub (a :: G) G :=
  fun b v => match v in var G' b' return
    match G' with
    | nil => unit
    | c :: G0 => tm G0 c -> tm G0 b'
    end with
  | @vz _ _ => fun u0 => u0
  | @vs _ _ _ w => fun _ => Var w
  end u.

Definition instantiate {G a b} (u : tm G a) (t : tm (a :: G) b) :=
  subst t (head_sub u).

(* The conversion judgment is SYNTACTIC, not arbitrary denotational equality.
   Congruence plus reflexive, symmetric, transitive beta conversion only. *)
Inductive beta : forall G a, tm G a -> tm G a -> Prop :=
| beta_refl : forall G a (t : tm G a), beta t t
| beta_sym : forall G a (t u : tm G a), beta t u -> beta u t
| beta_trans : forall G a (t u v : tm G a), beta t u -> beta u v -> beta t v
| beta_step : forall G a b (t : tm (a :: G) b) (u : tm G a),
    beta (App (Lam t) u) (instantiate u t)
| beta_lam : forall G a b (t u : tm (a :: G) b), beta t u -> beta (Lam t) (Lam u)
| beta_app : forall G a b (f g : tm G (arrow a b)) (x y : tm G a),
    beta f g -> beta x y -> beta (App f x) (App g y)
| beta_imp : forall G (p p' q q' : tm G truth),
    beta p p' -> beta q q' -> beta (Imp p q) (Imp p' q')
| beta_all : forall G a (p q : tm (a :: G) truth),
    beta p q -> beta (All p) (All q).

Definition falsity {G} : tm G truth := All (Var vz).
Definition neg {G} (p : tm G truth) := Imp p falsity.

(* Appendix A1.2's impredicative encodings, not extra inference rules. *)
Definition conj {G} (p q : tm G truth) : tm G truth :=
  All (Imp (Imp (weaken p) (Imp (weaken q) (Var vz))) (Var vz)).
Definition disj {G} (p q : tm G truth) : tm G truth :=
  All (Imp (Imp (weaken p) (Var vz))
           (Imp (Imp (weaken q) (Var vz)) (Var vz))).
Definition exists_ {G a} (p : tm (a :: G) truth) : tm G truth :=
  All (Imp (All (Imp
    (rename p (lift_ren (fun _ w => vs w)))
    (Var (vs vz)))) (Var vz)).

End Language.

Arguments Var {symbol G a} _.
Arguments Const {symbol G a} _.
Arguments Lam {symbol G a b} _.
Arguments App {symbol G a b} _ _.
Arguments Imp {symbol G} _ _.
Arguments All {symbol G a} _.
Arguments falsity {symbol G}.
