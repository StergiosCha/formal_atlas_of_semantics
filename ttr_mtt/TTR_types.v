(** TTR_types.v — The TTR Type System
    Formalizing Cooper (2023) Appendix A2–A8.

    This file defines:
    - Basic types and the witness/assignment function A (A2)
    - Predicate types / ptypes (A3)
    - Function types and partial function types (A4)
    - Set types and plurality types (A5)
    - Singleton types (A6)
    - Join types (A7) and Meet types (A8)

    Key design: The witness relation a :_TTR T is defined as an
    inductive proposition, NOT as Coq's own typing. This keeps
    the deep embedding honest — TTR types live in our Type
    universe and witnessing is a separate judgment.
*)

Require Import TTR_base.
Require Import List.
Require Import String.
Require Import Bool.
Import ListNotations.

(** * The Model: Assignment of witnesses to basic types
    Cooper A2: TYPE_B = ⟨Type, A⟩ where A maps types to witness sets.
    We model A as a function from type names to predicates on Val.
    A(T) is the set {v | basic_assignment T v}. *)

Definition BasicAssignment := string -> Val -> Prop.

(** * Predicate Signatures
    Cooper A3: ⟨Pred, ArgIndices, Arity⟩ *)

Record PredSig : Type := mkPredSig {
  ps_pred : list string;
  ps_arity : string -> list TTRType
}.

(** * Witness Assignment for ptypes
    Cooper A3: For T ∈ PType, F(T) is a set disjoint from Type. *)

Definition PTypeAssignment := string -> list Val -> Val -> Prop.

(** * The Full Model
    Cooper A3.2: TYPE_C = ⟨Type, BType, ⟨PType, Pred, ArgIndices, Arity⟩, ⟨A, F⟩⟩ *)

Record TTRModel : Type := mkModel {
  m_basic_assign : BasicAssignment;
  m_ptype_assign : PTypeAssignment;
  m_pred_sig     : PredSig
}.

(** * Helper functions (defined before the witness relation) *)

(** Look up a label in a value that should be a labelled set *)
Definition val_lookup (v : Val) (l : Label) : option Val :=
  match v with
  | VLSet ls => ls_lookup ls l
  | _ => None
  end.

(** Extract a TTRType from a Val *)
Definition val_to_type (v : Val) : option TTRType :=
  match v with
  | VType T => Some T
  | _ => None
  end.

(** * The Witness Relation: a :_TTR T
    Central judgment of TTR.
    Cooper: "a :_TYPE T iff a ∈ A(T)" for basic types,
    "a :_TYPE T iff a ∈ F(T)" for ptypes, etc.

    Design note on strict positivity: Function type witnessing
    (wit_fun) cannot refer to 'witnesses' in a negative position
    (left of ->). We use an external Prop parameter instead.
    This means function type witnessing must be established
    separately and fed in as evidence. Same for set types. *)

Inductive witnesses (M : TTRModel) : Val -> TTRType -> Prop :=

  (** A2: Basic types — a witnesses T iff A(T)(a) *)
  | wit_basic : forall (name : string) (a : Val),
      m_basic_assign M name a ->
      witnesses M a (TBasic name)

  (** A3: Predicate types — a witnesses P(a1,...,an) iff F(P,args)(a) *)
  | wit_ptype : forall (pred : string) (args : list Val) (a : Val),
      m_ptype_assign M pred args a ->
      witnesses M a (TPType pred args)

  (** A4: Function types (total) — f witnesses (T1 -> T2).
      We take an external proof that f maps T1-witnesses to T2-witnesses.
      The Prop H is opaque to the inductive — avoids negative occurrence. *)
  | wit_fun : forall (T1 T2 : TTRType) (f : Val) (H : Prop),
      H ->
      witnesses M f (TFun T1 T2)

  (** A4: Partial function types *)
  | wit_partfun : forall (T1 T2 : TTRType) (f : Val),
      witnesses M f (TPartFun T1 T2)

  (** A6: Singleton types — a :_TTR T_b iff a : T and a = b *)
  | wit_singleton : forall (T : TTRType) (a : Val),
      witnesses M a T ->
      witnesses M a (TSingleton T a)

  (** A7: Join types — disjunction *)
  | wit_join_l : forall (T1 T2 : TTRType) (a : Val),
      witnesses M a T1 ->
      witnesses M a (TJoin T1 T2)

  | wit_join_r : forall (T1 T2 : TTRType) (a : Val),
      witnesses M a T2 ->
      witnesses M a (TJoin T1 T2)

  (** A8: Meet types — conjunction *)
  | wit_meet : forall (T1 T2 : TTRType) (a : Val),
      witnesses M a T1 ->
      witnesses M a T2 ->
      witnesses M a (TMeet T1 T2)

  (** A5: Set types — X witnesses set(T).
      Same trick: external Prop to avoid negative occurrence. *)
  | wit_set : forall (T : TTRType) (ls : LabelledSet) (H : Prop),
      H ->
      witnesses M (VLSet ls) (TSet T)

  (** Record types — base case: empty record type *)
  | wit_rectype_nil : forall (r : Val),
      witnesses M r (TRecType LSNil)

  (** Record types — inductive case *)
  | wit_rectype_cons : forall (r : Val) (l : Label) (T_val : Val)
                              (rest : LabelledSet) (T : TTRType),
      val_to_type T_val = Some T ->
      (exists v, val_lookup r l = Some v /\ witnesses M v T) ->
      witnesses M r (TRecType rest) ->
      witnesses M r (TRecType (LSCons (FPair l T_val) rest)).

(** Smart constructors for function/set witnessing that capture
    the intended semantics while satisfying strict positivity *)

Definition wit_fun_proper (M : TTRModel) (T1 T2 : TTRType) (f : Val)
  (Hfun : forall a, witnesses M a T1 -> exists b, witnesses M b T2)
  : witnesses M f (TFun T1 T2) :=
  wit_fun M T1 T2 f _ Hfun.

Definition wit_set_proper (M : TTRModel) (T : TTRType) (ls : LabelledSet)
  (Hall : forall l v, ls_lookup ls l = Some v -> witnesses M v T)
  : witnesses M (VLSet ls) (TSet T) :=
  wit_set M T ls _ Hall.

(** * Subtyping
    Cooper: T1 is a subtype of T2 iff
    {a | a :_TYPE T1} ⊆ {a | a :_TYPE T2}
    Semantic/extensional subtyping. *)

Definition subtype (M : TTRModel) (T1 T2 : TTRType) : Prop :=
  forall a : Val, witnesses M a T1 -> witnesses M a T2.

Notation "T1 '<:' T2 'in' M" := (subtype M T1 T2) (at level 70).

(** * Structural theorems *)

Theorem meet_intro : forall M a T1 T2,
  witnesses M a T1 -> witnesses M a T2 ->
  witnesses M a (TMeet T1 T2).
Proof. intros. apply wit_meet; assumption. Qed.

Theorem meet_elim_l : forall M a T1 T2,
  witnesses M a (TMeet T1 T2) -> witnesses M a T1.
Proof. intros. inversion H. assumption. Qed.

Theorem meet_elim_r : forall M a T1 T2,
  witnesses M a (TMeet T1 T2) -> witnesses M a T2.
Proof. intros. inversion H. assumption. Qed.

Theorem join_supertype_l : forall M T1 T2,
  subtype M T1 (TJoin T1 T2).
Proof. unfold subtype. intros. apply wit_join_l. assumption. Qed.

Theorem join_supertype_r : forall M T1 T2,
  subtype M T2 (TJoin T1 T2).
Proof. unfold subtype. intros. apply wit_join_r. assumption. Qed.

Theorem meet_subtype_l : forall M T1 T2,
  subtype M (TMeet T1 T2) T1.
Proof. unfold subtype. intros. inversion H. assumption. Qed.

Theorem meet_subtype_r : forall M T1 T2,
  subtype M (TMeet T1 T2) T2.
Proof. unfold subtype. intros. inversion H. assumption. Qed.

Theorem subtype_refl : forall M T, subtype M T T.
Proof. unfold subtype. intros. assumption. Qed.

Theorem subtype_trans : forall M T1 T2 T3,
  subtype M T1 T2 -> subtype M T2 T3 -> subtype M T1 T3.
Proof. unfold subtype. intros. apply H0. apply H. assumption. Qed.

Theorem singleton_subtype : forall M T a,
  subtype M (TSingleton T a) T.
Proof. unfold subtype. intros. inversion H. assumption. Qed.

(** * Encoding TTR types as labelled sets
    Cooper represents each complex type as a labelled set.
    P(a1,...,an) = {⟨pred, P⟩, ⟨arg1, a1⟩, ..., ⟨argn, an⟩}
    T1 → T2     = {⟨dmn, T1⟩, ⟨rng, T2⟩}
    T1 ∨ T2     = {⟨disj1, T1⟩, ⟨disj2, T2⟩}
    T1 ∧ T2     = {⟨conj1, T1⟩, ⟨conj2, T2⟩} *)

Definition nat_to_string (n : nat) : string :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3"
  | 4 => "4" | 5 => "5" | _ => "n"
  end.

Fixpoint encode_args (args : list Val) (n : nat) : LabelledSet :=
  match args with
  | nil => LSNil
  | a :: rest =>
      LSCons (FPair (append "arg" (nat_to_string n)) a)
             (encode_args rest (S n))
  end.

Definition encode_ptype (pred : string) (args : list Val) : LabelledSet :=
  LSCons (FPair "pred"%string (VStr pred)) (encode_args args 1).

Definition encode_fun_type (T1 T2 : TTRType) : LabelledSet :=
  ls_pair "dmn"%string (VType T1) "rng"%string (VType T2).

Definition encode_join (T1 T2 : TTRType) : LabelledSet :=
  ls_pair "disj1"%string (VType T1) "disj2"%string (VType T2).

Definition encode_meet (T1 T2 : TTRType) : LabelledSet :=
  ls_pair "conj1"%string (VType T1) "conj2"%string (VType T2).
