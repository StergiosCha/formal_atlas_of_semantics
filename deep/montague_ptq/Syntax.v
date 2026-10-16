(* PTQ 1973, reprint pp. 18-20, 23, 25. Source-first reconstruction.
   Intrinsic de Bruijn binding is an encoding choice, not Montague's notation.
   Free variables and constants are independently numbered at every type. *)
From Coq Require Import List.
Import ListNotations.
Set Implicit Arguments.

Inductive ty := e | t | arr (a b : ty) | intens (a : ty).
Definition ty_eq_dec (a b : ty) : {a = b} + {a <> b}.
Proof. decide equality. Defined.
Inductive cat := ce | ct | slash (A B : cat) | dslash (A B : cat).
Fixpoint category_type (A : cat) : ty :=
  match A with
  | ce => e | ct => t
  | slash A B | dslash A B => arr (intens (category_type B)) (category_type A)
  end.
Definition IV := slash ct ce.
Definition NP := slash ct IV.
Definition TV := slash IV NP.
Definition CN := dslash ct ce.
Definition IAV := slash IV IV.
Definition ic := intens e.
Definition ivty := category_type IV.
Definition npty := category_type NP.

Example iv_type_from_source : category_type IV = arr ic t.
Proof. reflexivity. Qed.
Example cn_type_from_source : category_type CN = arr ic t.
Proof. reflexivity. Qed.
Example sentence_type_from_source : category_type ct = t.
Proof. reflexivity. Qed.
Example syntactic_categories_remain_distinct : IV <> CN.
Proof. discriminate. Qed.

Inductive var : list ty -> ty -> Type :=
| vz : forall G a, var (a :: G) a
| vs : forall G a b, var G a -> var (b :: G) a.
Arguments vz {G a}.
Arguments vs {G a b} _.

Lemma var_cases G a (P : forall b, var (a :: G) b -> Prop) :
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

Inductive tm : list ty -> ty -> Type :=
| Var : forall G a, var G a -> tm G a
| Free : forall G a, nat -> tm G a
| Con : forall G a, nat -> tm G a
| Lam : forall G a b, tm (a :: G) b -> tm G (arr a b)
| App : forall G a b, tm G (arr a b) -> tm G a -> tm G b
| Eq : forall G a, tm G a -> tm G a -> tm G t
| Neg : forall G, tm G t -> tm G t
| And : forall G, tm G t -> tm G t -> tm G t
| Or : forall G, tm G t -> tm G t -> tm G t
| Imp : forall G, tm G t -> tm G t -> tm G t
| Iff : forall G, tm G t -> tm G t -> tm G t
| All : forall G a, tm (a :: G) t -> tm G t
| Ex : forall G a, tm (a :: G) t -> tm G t
| Box : forall G, tm G t -> tm G t
| Will : forall G, tm G t -> tm G t
| Has : forall G, tm G t -> tm G t
| Up : forall G a, tm G a -> tm G (intens a)
| Down : forall G a, tm G (intens a) -> tm G a.
Arguments Var {G a} _.
Arguments Free {G a} _.
Arguments Con {G a} _.
Arguments Lam {G a b} _.
Arguments App {G a b} _ _.
Arguments Eq {G a} _ _.
Arguments Neg {G} _.
Arguments And {G} _ _.
Arguments Or {G} _ _.
Arguments Imp {G} _ _.
Arguments Iff {G} _ _.
Arguments All {G a} _.
Arguments Ex {G a} _.
Arguments Box {G} _.
Arguments Will {G} _.
Arguments Has {G} _.
Arguments Up {G a} _.
Arguments Down {G a} _.

Definition ren G D := forall a, var G a -> var D a.
Definition lift_ren {G D a} (r : ren G D) : ren (a :: G) (a :: D) :=
  fun b v => match v in var G' b' return
    match G' with
    | nil => unit
    | c :: G0 => ren G0 D -> var (c :: D) b'
    end with
  | @vz _ _ => fun _ => vz
  | @vs _ _ _ w => fun r0 => vs (r0 _ w)
  end r.
Fixpoint rename {G a} (u : tm G a) : forall D, ren G D -> tm D a :=
  match u in tm G' a' return forall D, ren G' D -> tm D a' with
  | Var v => fun D r => Var (r _ v)
  | Free n => fun D _ => Free n
  | Con n => fun D _ => Con n
  | Lam p => fun D r => Lam (rename p (lift_ren r))
  | App p q => fun D r => App (rename p r) (rename q r)
  | Eq p q => fun D r => Eq (rename p r) (rename q r)
  | Neg p => fun D r => Neg (rename p r)
  | And p q => fun D r => And (rename p r) (rename q r)
  | Or p q => fun D r => Or (rename p r) (rename q r)
  | Imp p q => fun D r => Imp (rename p r) (rename q r)
  | Iff p q => fun D r => Iff (rename p r) (rename q r)
  | All p => fun D r => All (rename p (lift_ren r))
  | Ex p => fun D r => Ex (rename p (lift_ren r))
  | Box p => fun D r => Box (rename p r)
  | Will p => fun D r => Will (rename p r)
  | Has p => fun D r => Has (rename p r)
  | Up p => fun D r => Up (rename p r)
  | Down p => fun D r => Down (rename p r)
  end.
Definition weaken {G a b} (u : tm G b) : tm (a :: G) b :=
  rename u (fun _ v => vs v).
