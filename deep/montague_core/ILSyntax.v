(* Specified world-only IL fragment, not the full legacy PTQ_deep2 language.
   Variables and constants denote fixed values; Up/Down expose world dependence.
   No tense, primitive equality, choice, or unrestricted IL beta conversion. *)
From Coq Require Import List.
From MontagueProof Require Import Ty2Syntax.
Import ListNotations.
Set Implicit Arguments.

Inductive ity := ie | it | iarr (a b : ity) | intens (a : ity).
Fixpoint world_type (a : ity) : wty :=
  match a with
  | ie => we | it => wt
  | iarr a b => warr (world_type a) (world_type b)
  | intens a => warr ws (world_type a)
  end.

Inductive ivar : list ity -> ity -> Type :=
| iz : forall G a, ivar (a :: G) a
| ivs : forall G a b, ivar G a -> ivar (b :: G) a.
Arguments iz {G a}.
Arguments ivs {G a b} _.

Lemma ivar_cons_cases G a (P : forall b, ivar (a :: G) b -> Prop) :
  P a iz -> (forall b (v : ivar G b), P b (ivs v)) -> forall b v, P b v.
Proof.
  intros Hz Hs b v; revert P Hz Hs.
  exact (match v as w in ivar D c return
    match D as D0 return ivar D0 c -> Prop with
    | [] => fun _ => True
    | d :: D0 => fun w0 => forall P : forall b, ivar (d :: D0) b -> Prop,
        P d iz -> (forall b v, P b (ivs v)) -> P c w0
    end w with
  | @iz _ _ => fun P Hz _ => Hz
  | @ivs _ _ _ w0 => fun P _ Hs => Hs _ w0
  end).
Qed.

Section Terms.
Variable symbol : ity -> Type.
Inductive itm : list ity -> ity -> Type :=
| IVar : forall G a, ivar G a -> itm G a
| IConst : forall G a, symbol a -> itm G a
| ILam : forall G a b, itm (a :: G) b -> itm G (iarr a b)
| IApp : forall G a b, itm G (iarr a b) -> itm G a -> itm G b
| IImp : forall G, itm G it -> itm G it -> itm G it
| IAll : forall G a, itm (a :: G) it -> itm G it
| IUp : forall G a, itm G a -> itm G (intens a)
| IDown : forall G a, itm G (intens a) -> itm G a
| IBox : forall G, itm G it -> itm G it.
End Terms.
Arguments IVar {symbol G a} _.
Arguments IConst {symbol G a} _.
Arguments ILam {symbol G a b} _.
Arguments IApp {symbol G a b} _ _.
Arguments IImp {symbol G} _ _.
Arguments IAll {symbol G a} _.
Arguments IUp {symbol G a} _.
Arguments IDown {symbol G a} _.
Arguments IBox {symbol G} _.

Definition ivmap G D := forall a, ivar G a -> wvar D (world_type a).
Definition ilift {G D a} (r : ivmap G D) : ivmap (a :: G) (world_type a :: D) :=
  fun b v => match v in ivar G' b' return
    match G' with
    | [] => unit
    | c :: G0 => ivmap G0 D -> wvar (world_type c :: D) (world_type b')
    end with
  | @iz _ _ => fun _ => wz
  | @ivs _ _ _ w => fun r0 => wvs (r0 _ w)
  end r.
Definition ishift {G D a} (r : ivmap G D) : ivmap G (a :: D) :=
  fun b v => wvs (r b v).
Fixpoint ivar_embed {G a} (v : ivar G a) : wvar (map world_type G) (world_type a) :=
  match v with iz => wz | ivs v => wvs (ivar_embed v) end.

Section Translation.
Context {symbol : ity -> Type} {target : wty -> Type}.
Variable constants : forall a, symbol a -> target (world_type a).

(* Current world is a TERM, not a distinguished untyped variable name.
   Under source binders both it and old variables shift. Under Up/Box only
   old variables shift, and a fresh world becomes the evaluation index. *)
Fixpoint explicit_world {G a} (t : itm symbol G a) : forall D,
  ivmap G D -> wtm target D ws -> wtm target D (world_type a) :=
  match t in itm _ G' a' return forall D,
    ivmap G' D -> wtm target D ws -> wtm target D (world_type a') with
  | IVar v => fun D r _ => WVar (r _ v)
  | IConst c => fun D _ _ => WConst (@constants _ c)
  | ILam t => fun D r w => WLam (explicit_world t (ilift r) (wweaken w))
  | IApp f x => fun D r w => WApp (explicit_world f r w) (explicit_world x r w)
  | IImp p q => fun D r w => WImp (explicit_world p r w) (explicit_world q r w)
  | IAll p => fun D r w => WAll (explicit_world p (ilift r) (wweaken w))
  | IUp t => fun D r _ => WLam (explicit_world t (ishift r) (WVar wz))
  | IDown t => fun D r w => WApp (explicit_world t r w) w
  | IBox p => fun D r _ => WAll (explicit_world p (ishift r) (WVar wz))
  end.

Definition translate_intension {G a} (t : itm symbol G a)
  : wtm target (map world_type G) (warr ws (world_type a)) :=
  WLam (explicit_world t (ishift (@ivar_embed G)) (WVar wz)).
End Translation.
