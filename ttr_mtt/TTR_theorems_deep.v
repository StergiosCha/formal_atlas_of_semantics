(** TTR_theorems_deep.v — Theorems in the deep embedding
    Parallel to TTR_theorems_shallow.v for comparison.

    PART A: Theorems that BOTH embeddings can prove
    PART B: Theorems ONLY the deep embedding can state/prove
*)

Require Import TTR_base.
Require Import TTR_types.
Require Import TTR_records.
Require Import List.
Require Import String.
Require Import Bool.
Import ListNotations.
Open Scope string_scope.

(** ============================================================ *)
(** PART A: Parallel theorems — same results as shallow version  *)
(** ============================================================ *)

Section ParallelTheorems.
  Variable M : TTRModel.

  (** --- A1: Basic inference: "Every man runs. John is a man. John runs." --- *)

  (** In the deep embedding, "every man runs" is a meta-level statement
      about the model: anything that witnesses man(x) also witnesses run(x). *)

  Hypothesis every_man_runs :
    forall x, m_ptype_assign M "man" [x] x ->
              m_ptype_assign M "run" [x] x.

  Hypothesis john_is_ind : m_basic_assign M "Ind" (VStr "john").
  Hypothesis john_is_man : m_ptype_assign M "man" [VStr "john"] (VStr "john").

  Theorem deep_john_runs :
    m_ptype_assign M "run" [VStr "john"] (VStr "john").
  Proof.
    apply every_man_runs. exact john_is_man.
  Qed.

  (** Lifted to witness relation *)
  Theorem deep_john_witnesses_run :
    witnesses M (VStr "john") (TPType "run" [VStr "john"]).
  Proof.
    apply wit_ptype. apply every_man_runs. exact john_is_man.
  Qed.

  (** --- A2: Record type subtyping (width) ---
      [ x : Ind, c : man(x) ] is a subtype of [ x : Ind ]
      i.e., any record witnessing the first also witnesses the second. *)

  Definition rt_man : RecType :=
    [ RF_plain "x" (TBasic "Ind") ;
      RF_dep "c_man" (fun v => TPType "man" [v]) [PLabel "x"] ].

  Definition rt_ind_only : RecType :=
    [ RF_plain "x" (TBasic "Ind") ].

  Theorem deep_width_subtyping : forall r,
    witnesses_rt M r rt_man -> witnesses_rt M r rt_ind_only.
  Proof.
    intros r H. inversion H; subst.
    apply wrt_plain.
    - assumption.
    - apply wrt_nil.
  Qed.

  (** --- A3: Meet is a subtype of both conjuncts --- *)

  Theorem deep_meet_sub_l : forall T1 T2,
    subtype M (TMeet T1 T2) T1.
  Proof.
    unfold subtype. intros. inversion H. assumption.
  Qed.

  Theorem deep_meet_sub_r : forall T1 T2,
    subtype M (TMeet T1 T2) T2.
  Proof.
    unfold subtype. intros. inversion H. assumption.
  Qed.

  (** --- A4: Join is a supertype of both disjuncts --- *)

  Theorem deep_join_sup_l : forall T1 T2,
    subtype M T1 (TJoin T1 T2).
  Proof.
    unfold subtype. intros. apply wit_join_l. assumption.
  Qed.

  (** --- A5: Singleton subtyping: T_a <: T --- *)

  Theorem deep_singleton_sub : forall T a,
    subtype M (TSingleton T a) T.
  Proof.
    unfold subtype. intros. inversion H. assumption.
  Qed.

  (** --- A6: Transitivity of subtyping --- *)

  Theorem deep_sub_trans : forall T1 T2 T3,
    subtype M T1 T2 -> subtype M T2 T3 -> subtype M T1 T3.
  Proof.
    unfold subtype. intros. apply H0. apply H. assumption.
  Qed.

End ParallelTheorems.


(** ============================================================ *)
(** PART B: Theorems ONLY the deep embedding can state           *)
(** ============================================================ *)

(** --- B1: Types as first-class values ---
    We can store a type inside a record and retrieve it.
    This is impossible in the shallow embedding. *)

Definition type_bearing_record : Val :=
  VLSet (ls_pair "content" (VStr "hello")
                 "type"    (VType (TBasic "Greeting"))).

Theorem deep_type_recovery :
  val_lookup type_bearing_record "type" = Some (VType (TBasic "Greeting")).
Proof. reflexivity. Qed.

(** A record whose field VALUE is itself a type.
    In Cooper's framework, this is essential for information states
    where agents track which types they believe are inhabited. *)


(** --- B2: Merge of record types ---
    Given two record types, compute their merge.
    Cannot even be stated in the shallow embedding. *)

Definition rt1 : RecType := [ RF_plain "x" (TBasic "Ind") ].
Definition rt2 : RecType := [ RF_plain "y" (TBasic "Ind") ].
Definition rt_merged : RecType := rt_merge_simple rt1 rt2.

Theorem deep_merge_result :
  rt_merged = [ RF_plain "x" (TBasic "Ind") ;
                RF_plain "y" (TBasic "Ind") ].
Proof. reflexivity. Qed.

(** Merge with overlapping labels: rt2 wins *)
Definition rt3 : RecType := [ RF_plain "x" (TBasic "Ind") ;
                               RF_plain "z" (TBasic "Real") ].
Definition rt4 : RecType := [ RF_plain "x" (TBasic "Human") ;
                               RF_plain "w" (TBasic "Ind") ].
Definition rt_merged2 : RecType := rt_merge_simple rt3 rt4.

Theorem deep_merge_overlap :
  rt_merged2 = [ RF_plain "z" (TBasic "Real") ;
                 RF_plain "x" (TBasic "Human") ;
                 RF_plain "w" (TBasic "Ind") ].
Proof. reflexivity. Qed.

(** --- B3: Types without witnesses ---
    We can define a model where a specific type has no witnesses
    and PROVE that fact. In shallow Coq, you can't reason about
    whether a type is inhabited without extra axioms. *)

Section EmptyTypes.
  (** A model that assigns nothing to "Unicorn" *)
  Variable M_empty : TTRModel.
  Hypothesis no_unicorns :
    forall a, ~ m_basic_assign M_empty "Unicorn" a.

  (** No value witnesses the type "Unicorn" via wit_basic *)
  Theorem deep_no_unicorn_witnesses :
    forall a, ~ witnesses M_empty a (TBasic "Unicorn").
  Proof.
    intros a H. inversion H; subst.
    eapply no_unicorns. eassumption.
  Qed.

  (** But the type TBasic "Unicorn" still EXISTS as a value —
      we can store it, compare it, manipulate it.
      In the shallow embedding, an uninhabited type is just False
      and carries no structure. *)

  Theorem deep_unicorn_is_structured :
    val_to_type (VType (TBasic "Unicorn")) = Some (TBasic "Unicorn").
  Proof. reflexivity. Qed.
End EmptyTypes.


(** --- B4: Relabelling ---
    Two record types identical except for labels.
    In deep: we can define structural equivalence.
    In shallow: they are irreconcilably different Coq types. *)

Definition rt_agent : RecType := [ RF_plain "agent" (TBasic "Ind") ].
Definition rt_actor : RecType := [ RF_plain "actor" (TBasic "Ind") ].

(** These are structurally identical (one Ind field) but
    have different labels. We can define and prove this: *)
Definition same_field_types (r1 r2 : RecType) : Prop :=
  List.length r1 = List.length r2.
  (* A real version would check type-by-type structural equality.
     Simplified here for illustration. *)

Theorem deep_relabel_equivalent :
  same_field_types rt_agent rt_actor.
Proof. reflexivity. Qed.


(** --- B5: Type equality is decidable ---
    Since TTRType is an inductive data type, we can in principle
    define decidable equality on it. In the shallow embedding,
    type equality is not even expressible at the object level. *)

(** We can at least compare basic types: *)
Definition ttrtype_eq_basic (t1 t2 : TTRType) : bool :=
  match t1, t2 with
  | TBasic s1, TBasic s2 => String.eqb s1 s2
  | _, _ => false
  end.

Theorem deep_type_eq_refl :
  ttrtype_eq_basic (TBasic "Ind") (TBasic "Ind") = true.
Proof. reflexivity. Qed.

Theorem deep_type_eq_diff :
  ttrtype_eq_basic (TBasic "Ind") (TBasic "Human") = false.
Proof. reflexivity. Qed.


(** --- B6: Reasoning across models ---
    A type that is inhabited in one model but not another.
    The deep embedding's model parameter makes this natural.
    The shallow embedding has no model parameter. *)

Section CrossModel.
  Variable M1 M2 : TTRModel.

  Hypothesis M1_has_dragons :
    m_basic_assign M1 "Dragon" (VStr "smaug").
  Hypothesis M2_no_dragons :
    forall a, ~ m_basic_assign M2 "Dragon" a.

  (** Dragon is possible (inhabited in some model) *)
  Theorem deep_dragon_possible :
    witnesses M1 (VStr "smaug") (TBasic "Dragon").
  Proof.
    apply wit_basic. exact M1_has_dragons.
  Qed.

  (** Dragon is not necessary (not inhabited in all models) *)
  Theorem deep_dragon_not_necessary :
    ~ witnesses M2 (VStr "smaug") (TBasic "Dragon").
  Proof.
    intro H. inversion H; subst.
    eapply M2_no_dragons. eassumption.
  Qed.
End CrossModel.
