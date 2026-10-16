(* Explicit-index higher-order target. Separate world/time/index sorts,
   ordinary typed lambda, Prop-valued logical primitives. Not Boolean Ty2. *)
From Coq Require Import List.
Import ListNotations.
Set Implicit Arguments.

Inductive pty := pe | pt | pw | ptime | pi | parr (a b : pty).
Inductive pvar : list pty -> pty -> Type :=
| pz : forall G a, pvar (a :: G) a
| pvs : forall G a b, pvar G a -> pvar (b :: G) a.
Arguments pz {G a}.
Arguments pvs {G a b} _.

Lemma pvar_cons_cases G a (P : forall b, pvar (a :: G) b -> Prop) :
  P a pz -> (forall b (v : pvar G b), P b (pvs v)) -> forall b v, P b v.
Proof.
  intros Hz Hs b v; revert P Hz Hs.
  exact (match v as w in pvar D c return
    match D as D0 return pvar D0 c -> Prop with
    | [] => fun _ => True
    | d :: D0 => fun w0 => forall P : forall b, pvar (d :: D0) b -> Prop,
        P d pz -> (forall b v, P b (pvs v)) -> P c w0
    end w with
  | @pz _ _ => fun P Hz _ => Hz
  | @pvs _ _ _ w0 => fun P _ Hs => Hs _ w0
  end).
Qed.

Section Terms.
Variable symbol : pty -> Type.
Inductive ptm : list pty -> pty -> Type :=
| PVar : forall G a, pvar G a -> ptm G a
| PConst : forall G a, symbol a -> ptm G a
| PLam : forall G a b, ptm (a :: G) b -> ptm G (parr a b)
| PApp : forall G a b, ptm G (parr a b) -> ptm G a -> ptm G b
| PEq : forall G a, ptm G a -> ptm G a -> ptm G pt
| PNot : forall G, ptm G pt -> ptm G pt
| PAnd : forall G, ptm G pt -> ptm G pt -> ptm G pt
| POr : forall G, ptm G pt -> ptm G pt -> ptm G pt
| PImp : forall G, ptm G pt -> ptm G pt -> ptm G pt
| PIff : forall G, ptm G pt -> ptm G pt -> ptm G pt
| PAll : forall G a, ptm (a :: G) pt -> ptm G pt
| PExists : forall G a, ptm (a :: G) pt -> ptm G pt
| PPair : forall G, ptm G pw -> ptm G ptime -> ptm G pi
| PWorld : forall G, ptm G pi -> ptm G pw
| PTime : forall G, ptm G pi -> ptm G ptime
| PBefore : forall G, ptm G ptime -> ptm G ptime -> ptm G pt.
End Terms.
Arguments PVar {symbol G a} _.
Arguments PConst {symbol G a} _.
Arguments PLam {symbol G a b} _.
Arguments PApp {symbol G a b} _ _.
Arguments PEq {symbol G a} _ _.
Arguments PNot {symbol G} _.
Arguments PAnd {symbol G} _ _.
Arguments POr {symbol G} _ _.
Arguments PImp {symbol G} _ _.
Arguments PIff {symbol G} _ _.
Arguments PAll {symbol G a} _.
Arguments PExists {symbol G a} _.
Arguments PPair {symbol G} _ _.
Arguments PWorld {symbol G} _.
Arguments PTime {symbol G} _.
Arguments PBefore {symbol G} _ _.

Definition pren G D := forall a, pvar G a -> pvar D a.
Definition plift {G D a} (r : pren G D) : pren (a :: G) (a :: D) :=
  fun b v => match v in pvar G' b' return
    match G' with
    | [] => unit
    | c :: G0 => pren G0 D -> pvar (c :: D) b'
    end with
  | @pz _ _ => fun _ => pz
  | @pvs _ _ _ w => fun r0 => pvs (r0 _ w)
  end r.
Fixpoint prename {symbol G a} (t : ptm symbol G a) : forall D, pren G D -> ptm symbol D a :=
  match t in ptm _ G' a' return forall D, pren G' D -> ptm symbol D a' with
  | PVar v => fun D r => PVar (r _ v)
  | PConst c => fun D _ => PConst c
  | PLam t => fun D r => PLam (prename t (plift r))
  | PApp f x => fun D r => PApp (prename f r) (prename x r)
  | PEq x y => fun D r => PEq (prename x r) (prename y r)
  | PNot p => fun D r => PNot (prename p r)
  | PAnd p q => fun D r => PAnd (prename p r) (prename q r)
  | POr p q => fun D r => POr (prename p r) (prename q r)
  | PImp p q => fun D r => PImp (prename p r) (prename q r)
  | PIff p q => fun D r => PIff (prename p r) (prename q r)
  | PAll p => fun D r => PAll (prename p (plift r))
  | PExists p => fun D r => PExists (prename p (plift r))
  | PPair w t => fun D r => PPair (prename w r) (prename t r)
  | PWorld i => fun D r => PWorld (prename i r)
  | PTime i => fun D r => PTime (prename i r)
  | PBefore s t => fun D r => PBefore (prename s r) (prename t r)
  end.
Definition pweaken {symbol G a b} (t : ptm symbol G b) : ptm symbol (a :: G) b :=
  prename t (fun _ v => pvs v).
