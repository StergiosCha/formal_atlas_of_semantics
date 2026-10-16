(* Gallin (1975), section 2 and Theorem 8.2: untensed IL has arbitrary
   inhabited entity and index carriers, not a required world-time product.
   This syntax embeds into the actual PTQ syntax but has no Will or Has. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types.
Import ListNotations.
Set Implicit Arguments.

Inductive itm : list ty -> ty -> Type :=
| IVar : forall G a, var G a -> itm G a
| IFree : forall G a, nat -> itm G a
| ICon : forall G a, nat -> itm G a
| ILam : forall G a b, itm (a :: G) b -> itm G (arr a b)
| IApp : forall G a b, itm G (arr a b) -> itm G a -> itm G b
| IEq : forall G a, itm G a -> itm G a -> itm G t
| INeg : forall G, itm G t -> itm G t
| IAnd : forall G, itm G t -> itm G t -> itm G t
| IOr : forall G, itm G t -> itm G t -> itm G t
| IImp : forall G, itm G t -> itm G t -> itm G t
| IIff : forall G, itm G t -> itm G t -> itm G t
| IAll : forall G a, itm (a :: G) t -> itm G t
| IEx : forall G a, itm (a :: G) t -> itm G t
| IBox : forall G, itm G t -> itm G t
| IUp : forall G a, itm G a -> itm G (intens a)
| IDown : forall G a, itm G (intens a) -> itm G a.
Arguments IVar {G a} _.
Arguments IFree {G a} _.
Arguments ICon {G a} _.
Arguments ILam {G a b} _.
Arguments IApp {G a b} _ _.
Arguments IEq {G a} _ _.
Arguments INeg {G} _.
Arguments IAnd {G} _ _.
Arguments IOr {G} _ _.
Arguments IImp {G} _ _.
Arguments IIff {G} _ _.
Arguments IAll {G a} _.
Arguments IEx {G a} _.
Arguments IBox {G} _.
Arguments IUp {G a} _.
Arguments IDown {G a} _.

Fixpoint embed_il {G a} (p : itm G a) : tm G a :=
  match p with
  | IVar v => Var v | IFree n => Free n | ICon n => Con n
  | ILam p => Lam (embed_il p) | IApp p q => App (embed_il p) (embed_il q)
  | IEq p q => Eq (embed_il p) (embed_il q) | INeg p => Neg (embed_il p)
  | IAnd p q => And (embed_il p) (embed_il q)
  | IOr p q => Or (embed_il p) (embed_il q)
  | IImp p q => Imp (embed_il p) (embed_il q)
  | IIff p q => Iff (embed_il p) (embed_il q)
  | IAll p => All (embed_il p) | IEx p => Ex (embed_il p)
  | IBox p => Box (embed_il p) | IUp p => Up (embed_il p) | IDown p => Down (embed_il p)
  end.
Fixpoint is_untensed {G a} (p : tm G a) : bool :=
  match p with
  | Var _ | Free _ | Con _ => true
  | Will _ | Has _ => false
  | Lam p | Neg p | All p | Ex p | Box p | Up p | Down p => is_untensed p
  | App p q | Eq p q | And p q | Or p q | Imp p q | Iff p q =>
      andb (is_untensed p) (is_untensed q)
  end.
Theorem embedded_il_is_untensed G a (p : itm G a) : is_untensed (embed_il p) = true.
Proof. induction p; cbn; try reflexivity; try assumption.
  all: rewrite IHp1, IHp2; reflexivity. Qed.

Fixpoint idomain (E I : Type) (a : ty) : Type :=
  match a with
  | e => E | t => bool
  | arr a b => idomain E I a -> idomain E I b
  | intens a => I -> idomain E I a
  end.
Record il_model := {
  il_entities : Type; il_indices : Type;
  il_entities_inhabited : inhabited il_entities;
  il_indices_inhabited : inhabited il_indices;
  il_truth : BooleanTruth;
  il_extensionality : FunExt;
  il_constants : forall a, nat -> il_indices -> idomain il_entities il_indices a
}.
Definition il_free_env M := forall a, nat -> idomain (il_entities M) (il_indices M) a.
Definition il_env M G := forall a, var G a -> idomain (il_entities M) (il_indices M) a.
Definition il_extend {M G a} (rho : il_env M G)
  (x : idomain (il_entities M) (il_indices M) a) : il_env M (a :: G) :=
  fun b v => match v in var G' b' return
    match G' with [] => unit
    | c :: G0 => il_env M G0 -> idomain (il_entities M) (il_indices M) c ->
      idomain (il_entities M) (il_indices M) b' end with
  | @vz _ _ => fun _ x0 => x0
  | @vs _ _ _ w => fun r _ => r _ w
  end rho x.
Definition il_empty M : il_env M [] := fun a v =>
  match v in var G b return match G with
    [] => idomain (il_entities M) (il_indices M) b | _ => unit end with
  | vz => tt | vs _ => tt end.

Fixpoint ieval (M : il_model) {G a} (p : itm G a) (rho : il_env M G)
  (sigma : il_free_env M) (i : il_indices M) : idomain (il_entities M) (il_indices M) a :=
  match p in itm G' a' return il_env M G' -> idomain (il_entities M) (il_indices M) a' with
  | IVar v => fun r => r _ v
  | IFree n => fun _ => sigma _ n | ICon n => fun _ => il_constants M _ n i
  | ILam p => fun r x => ieval p (il_extend r x) sigma i
  | IApp p q => fun r => ieval p r sigma i (ieval q r sigma i)
  | IEq p q => fun r => truth (il_truth M) (ieval p r sigma i = ieval q r sigma i)
  | INeg p => fun r => negb (ieval p r sigma i)
  | IAnd p q => fun r => andb (ieval p r sigma i) (ieval q r sigma i)
  | IOr p q => fun r => orb (ieval p r sigma i) (ieval q r sigma i)
  | IImp p q => fun r => orb (negb (ieval p r sigma i)) (ieval q r sigma i)
  | IIff p q => fun r => Bool.eqb (ieval p r sigma i) (ieval q r sigma i)
  | IAll p => fun r => truth (il_truth M) (forall x, ieval p (il_extend r x) sigma i = true)
  | IEx p => fun r => truth (il_truth M) (exists x, ieval p (il_extend r x) sigma i = true)
  | IBox p => fun r => truth (il_truth M) (forall j, ieval p r sigma j = true)
  | IUp p => fun r j => ieval p r sigma j
  | IDown p => fun r => ieval p r sigma i i
  end rho.
Arguments ieval M {G a} p rho sigma i.

(* Separate recursors for the source and target domains; transports are
   justified by structural equality, with no appeal to a world-time frame. *)
Fixpoint il_domain_agreement E I a : idomain E I a = value_domain E I (translate_type a) :=
  match a with
  | e => eq_refl | t => eq_refl
  | arr a b => arrow_eq (il_domain_agreement E I a) (il_domain_agreement E I b)
  | intens a => arrow_eq eq_refl (il_domain_agreement E I a)
  end.
Definition il_lift E I a := cast (il_domain_agreement E I a).
Definition il_lower E I a := cast (eq_sym (il_domain_agreement E I a)).
Lemma il_lower_lift E I a x : il_lower E I a (il_lift E I a x) = x.
Proof. apply cast_back. Qed.
Lemma il_lift_lower E I a x : il_lift E I a (il_lower E I a x) = x.
Proof. apply cast_forward. Qed.
Lemma il_lift_application E I a b (f : idomain E I (arr a b)) x :
  il_lift E I (arr a b) f (il_lift E I a x) = il_lift E I b (f x).
Proof. apply cast_application. Qed.
Lemma il_lift_lambda E I a b (f : idomain E I (arr a b)) :
  il_lift E I (arr a b) f = fun x => il_lift E I b (f (il_lower E I a x)).
Proof. apply cast_lambda. Qed.
Lemma il_lift_intension E I a (f : idomain E I (intens a)) :
  il_lift E I (intens a) f = fun i => il_lift E I a (f i).
Proof. apply cast_lambda. Qed.

Definition forget_ptq_time (M : model) : il_model :=
  {| il_entities := entity (carrier M); il_indices := index (carrier M);
     il_entities_inhabited := entity_nonempty (carrier M);
     il_indices_inhabited :=
       match world_nonempty (carrier M), time_nonempty (carrier M) with
       | inhabits w, inhabits j => inhabits (w,j) end;
     il_truth := boolean_truth M; il_extensionality := function_extensionality M;
     il_constants := fun a n i => il_lower (entity (carrier M)) (index (carrier M)) a
       (lift_value (carrier M) a (constants M a n i)) |}.
Definition forget_ptq_env M G (rho : env M G) : il_env (forget_ptq_time M) G :=
  fun a v => il_lower (entity (carrier M)) (index (carrier M)) a
    (lift_value (carrier M) a (rho a v)).
Definition forget_ptq_free M (sigma : free_env M) : il_free_env (forget_ptq_time M) :=
  fun a n => il_lower (entity (carrier M)) (index (carrier M)) a
    (lift_value (carrier M) a (sigma a n)).
