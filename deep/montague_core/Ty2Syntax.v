(* Selected Ty2 fragment: e, t, s and arrows; implication/quantification
   follow C. Source: Hahn/Richter 2015 pp. 516-518 and C&L 2020 pp. 9-10.
   No implicit evaluation index, tense, choice, primitive equality or eta. *)
From Coq Require Import List.
Import ListNotations.
Set Implicit Arguments.

Inductive wty := we | wt | ws | warr (a b : wty).
Inductive wvar : list wty -> wty -> Type :=
| wz : forall G a, wvar (a :: G) a
| wvs : forall G a b, wvar G a -> wvar (b :: G) a.
Arguments wz {G a}.
Arguments wvs {G a b} _.

Lemma wvar_cons_cases G a (P : forall b, wvar (a :: G) b -> Prop) :
  P a wz -> (forall b (v : wvar G b), P b (wvs v)) -> forall b v, P b v.
Proof.
  intros Hz Hs b v; revert P Hz Hs.
  exact (match v as w in wvar D c return
    match D as D0 return wvar D0 c -> Prop with
    | [] => fun _ => True
    | d :: D0 => fun w0 => forall P : forall b, wvar (d :: D0) b -> Prop,
        P d wz -> (forall b v, P b (wvs v)) -> P c w0
    end w with
  | @wz _ _ => fun P Hz _ => Hz
  | @wvs _ _ _ w0 => fun P _ Hs => Hs _ w0
  end).
Qed.

Section Terms.
Variable symbol : wty -> Type.
Inductive wtm : list wty -> wty -> Type :=
| WVar : forall G a, wvar G a -> wtm G a
| WConst : forall G a, symbol a -> wtm G a
| WLam : forall G a b, wtm (a :: G) b -> wtm G (warr a b)
| WApp : forall G a b, wtm G (warr a b) -> wtm G a -> wtm G b
| WImp : forall G, wtm G wt -> wtm G wt -> wtm G wt
| WAll : forall G a, wtm (a :: G) wt -> wtm G wt.
Arguments WVar {G a} _.
Arguments WConst {G a} _.
Arguments WLam {G a b} _.
Arguments WApp {G a b} _ _.
Arguments WImp {G} _ _.
Arguments WAll {G a} _.

Definition wren G D := forall a, wvar G a -> wvar D a.
Definition wlift_ren {G D a} (r : wren G D) : wren (a :: G) (a :: D) :=
  fun b v => match v in wvar G' b' return
    match G' with
    | [] => unit
    | c :: G0 => wren G0 D -> wvar (c :: D) b'
    end with
  | @wz _ _ => fun _ => wz
  | @wvs _ _ _ w => fun r0 => wvs (r0 _ w)
  end r.

Fixpoint wrename {G a} (t : wtm G a) : forall D, wren G D -> wtm D a :=
  match t in wtm G' a' return forall D, wren G' D -> wtm D a' with
  | WVar v => fun D r => WVar (r _ v)
  | WConst c => fun D _ => WConst c
  | WLam t => fun D r => WLam (wrename t (wlift_ren r))
  | WApp f x => fun D r => WApp (wrename f r) (wrename x r)
  | WImp p q => fun D r => WImp (wrename p r) (wrename q r)
  | WAll p => fun D r => WAll (wrename p (wlift_ren r))
  end.
Definition wweaken {G a b} (t : wtm G b) : wtm (a :: G) b :=
  wrename t (fun _ v => wvs v).

Definition wsub G D := forall a, wvar G a -> wtm D a.
Definition wlift_sub {G D a} (s : wsub G D) : wsub (a :: G) (a :: D) :=
  fun b v => match v in wvar G' b' return
    match G' with
    | [] => unit
    | c :: G0 => wsub G0 D -> wtm (c :: D) b'
    end with
  | @wz _ _ => fun _ => WVar wz
  | @wvs _ _ _ w => fun s0 => wweaken (s0 _ w)
  end s.
Fixpoint wsubst {G a} (t : wtm G a) : forall D, wsub G D -> wtm D a :=
  match t in wtm G' a' return forall D, wsub G' D -> wtm D a' with
  | WVar v => fun D s => s _ v
  | WConst c => fun D _ => WConst c
  | WLam t => fun D s => WLam (wsubst t (wlift_sub s))
  | WApp f x => fun D s => WApp (wsubst f s) (wsubst x s)
  | WImp p q => fun D s => WImp (wsubst p s) (wsubst q s)
  | WAll p => fun D s => WAll (wsubst p (wlift_sub s))
  end.
Definition whead_sub {G a} (u : wtm G a) : wsub (a :: G) G :=
  fun b v => match v in wvar G' b' return
    match G' with
    | [] => unit
    | c :: G0 => wtm G0 c -> wtm G0 b'
    end with
  | @wz _ _ => fun u0 => u0
  | @wvs _ _ _ w => fun _ => WVar w
  end u.
Definition winstantiate {G a b} (u : wtm G a) (t : wtm (a :: G) b) :=
  wsubst t (whead_sub u).

Inductive wbeta : forall G a, wtm G a -> wtm G a -> Prop :=
| wb_refl : forall G a (t : wtm G a), wbeta t t
| wb_sym : forall G a (t u : wtm G a), wbeta t u -> wbeta u t
| wb_trans : forall G a (t u v : wtm G a), wbeta t u -> wbeta u v -> wbeta t v
| wb_step : forall G a b (t : wtm (a :: G) b) u,
    wbeta (WApp (WLam t) u) (winstantiate u t)
| wb_lam : forall G a b (t u : wtm (a :: G) b), wbeta t u -> wbeta (WLam t) (WLam u)
| wb_app : forall G a b (f g : wtm G (warr a b)) x y,
    wbeta f g -> wbeta x y -> wbeta (WApp f x) (WApp g y)
| wb_imp : forall G (p q r s : wtm G wt),
    wbeta p q -> wbeta r s -> wbeta (WImp p r) (WImp q s)
| wb_all : forall G a (p q : wtm (a :: G) wt), wbeta p q -> wbeta (WAll p) (WAll q).

Definition wfalsity {G} : wtm G wt := WAll (WVar wz).
Definition wneg {G} (p : wtm G wt) := WImp p wfalsity.

(* Absolute necessity quantifies over ALL worlds. No accessibility relation
   or modal inference rule is silently installed. *)
Definition necessarily {G} (p : wtm G (warr ws wt)) : wtm G wt :=
  WAll (WApp (wweaken p) (WVar wz)).
Definition at_world {G a} (p : wtm G (warr ws a)) (w : wtm G ws) := WApp p w.

End Terms.
Arguments WVar {symbol G a} _.
Arguments WConst {symbol G a} _.
Arguments WLam {symbol G a b} _.
Arguments WApp {symbol G a b} _ _.
Arguments WImp {symbol G} _ _.
Arguments WAll {symbol G a} _.
Arguments wfalsity {symbol G}.
