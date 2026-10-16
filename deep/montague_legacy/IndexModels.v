(* Parameterized Prop interpretation; no implicit evaluation index. *)
From Coq Require Import List.
From MontagueProof Require Import Models.
From MontagueLegacy Require Import IndexSyntax.
Import ListNotations.
Set Implicit Arguments.

Fixpoint pdomain (E W T : Type) (a : pty) : Type :=
  match a with
  | pe => E | pt => Prop | pw => W | ptime => T | pi => (W * T)%type
  | parr a b => pdomain E W T a -> pdomain E W T b
  end.

Section Interpretation.
Context {symbol : pty -> Type} {E W T : Type}.
Variable lex : forall a, symbol a -> pdomain E W T a.
Variable before : T -> T -> Prop.

Definition penv G := forall a, pvar G a -> pdomain E W T a.
Definition pextend {G a} (rho : penv G) (x : pdomain E W T a) : penv (a :: G) :=
  fun b v => match v in pvar G' b' return
    match G' with
    | [] => unit
    | c :: G0 => penv G0 -> pdomain E W T c -> pdomain E W T b'
    end with
  | @pz _ _ => fun _ x0 => x0
  | @pvs _ _ _ w => fun rho0 _ => rho0 _ w
  end rho x.

Fixpoint peval {G a} (t : ptm symbol G a) : penv G -> pdomain E W T a :=
  match t in ptm _ G' a' return penv G' -> pdomain E W T a' with
  | PVar v => fun rho => rho _ v
  | PConst c => fun _ => @lex _ c
  | PLam t => fun rho x => peval t (pextend rho x)
  | PApp f x => fun rho => peval f rho (peval x rho)
  | PEq x y => fun rho => peval x rho = peval y rho
  | PNot p => fun rho => ~ peval p rho
  | PAnd p q => fun rho => peval p rho /\ peval q rho
  | POr p q => fun rho => peval p rho \/ peval q rho
  | PImp p q => fun rho => peval p rho -> peval q rho
  | PIff p q => fun rho => peval p rho <-> peval q rho
  | PAll p => fun rho => forall x, peval p (pextend rho x)
  | PExists p => fun rho => exists x, peval p (pextend rho x)
  | PPair w t => fun rho => (peval w rho, peval t rho)
  | PWorld i => fun rho => fst (peval i rho)
  | PTime i => fun rho => snd (peval i rho)
  | PBefore s t => fun rho => before (peval s rho) (peval t rho)
  end.

Lemma peval_rename (FE : FunExt) : forall G a (t : ptm symbol G a)
  D (r : pren G D) (rho : penv D) (sigma : penv G),
  (forall b v, sigma b v = rho b (r b v)) ->
  peval (prename t r) rho = peval t sigma.
Proof.
  intros G a t; induction t; intros D r rho sigma H; cbn;
    try (rewrite (IHt1 _ r rho sigma H), (IHt2 _ r rho sigma H); reflexivity);
    try (rewrite (IHt _ r rho sigma H); reflexivity).
  - symmetry; apply H.
  - reflexivity.
  - apply FE; intro x; apply IHt; apply pvar_cons_cases;
      cbn; [reflexivity | intros; apply H].
  - apply (f_equal (fun f : pdomain E W T a -> Prop => forall x, f x)).
    apply FE; intro x; apply IHt; apply pvar_cons_cases;
      cbn; [reflexivity | intros; apply H].
  - apply (f_equal (fun f : pdomain E W T a -> Prop => exists x, f x)).
    apply FE; intro x; apply IHt; apply pvar_cons_cases;
      cbn; [reflexivity | intros; apply H].
Qed.

Lemma peval_weaken (FE : FunExt) : forall G a b (t : ptm symbol G b)
  (rho : penv G) (x : pdomain E W T a),
  peval (pweaken t) (pextend rho x) = peval t rho.
Proof. intros; apply peval_rename; [exact FE | intros; reflexivity]. Qed.
End Interpretation.
Arguments peval {symbol E W T} lex before {G a} _ _.

(* Transport along equality of carriers, NOT an arbitrary isomorphism or
   a proposition-extensionality principle. These generic laws need no FE. *)
Definition carrier_cast {A B : Type} (p : A = B) (x : A) : B :=
  match p with eq_refl => x end.
Definition arrow_carrier {A B C D : Type} (p : A = B) (q : C = D) :
  (A -> C) = (B -> D).
Proof. destruct p, q; reflexivity. Defined.

Lemma cast_back {A B : Type} (p : A = B) (x : A) :
  carrier_cast (eq_sym p) (carrier_cast p x) = x.
Proof. destruct p; reflexivity. Qed.
Lemma cast_forward {A B : Type} (p : A = B) (x : B) :
  carrier_cast p (carrier_cast (eq_sym p) x) = x.
Proof. destruct p; reflexivity. Qed.
Lemma cast_application {A B C D : Type} (p : A = B) (q : C = D) (f : A -> C) x :
  carrier_cast (arrow_carrier p q) f (carrier_cast p x) = carrier_cast q (f x).
Proof. destruct p, q; reflexivity. Qed.
Lemma cast_lambda {A B C D : Type} (p : A = B) (q : C = D) (f : A -> C) :
  carrier_cast (arrow_carrier p q) f =
  fun x => carrier_cast q (f (carrier_cast (eq_sym p) x)).
Proof. destruct p, q; reflexivity. Qed.
Lemma cast_equality {A B : Type} (p : A = B) (x y : A) :
  (carrier_cast p x = carrier_cast p y) = (x = y).
Proof. destruct p; reflexivity. Qed.
Lemma cast_forall {A B : Type} (p : A = B) (f : A -> Prop) :
  (forall y, f (carrier_cast (eq_sym p) y)) = (forall x, f x).
Proof. destruct p; reflexivity. Qed.
Lemma cast_exists {A B : Type} (p : A = B) (f : A -> Prop) :
  (exists y, f (carrier_cast (eq_sym p) y)) = (exists x, f x).
Proof. destruct p; reflexivity. Qed.
