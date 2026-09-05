(** TTR_theorems_shallow.v — Theorems in the shallow embedding
    Parallel to TTR_theorems_deep.v for comparison.

    PART A: Same theorems as deep — both prove the same thing
    PART B: Theorems where shallow is CLEANER than deep
    PART C: Things the shallow embedding CANNOT do (marked Abort)
*)

Require Import String.
Require Import List.
Import ListNotations.

(** ============================================================ *)
(** Setup: the shallow TTR universe                              *)
(** ============================================================ *)

Parameter Ind : Set.
Parameter john : Ind.
Parameter man : Ind -> Prop.
Parameter run : Ind -> Prop.
Parameter walk : Ind -> Prop.
Parameter dog : Ind -> Prop.
Parameter cat : Ind -> Prop.
Parameter love : Ind -> Ind -> Prop.

(** Record types *)
Record ManRuns := mkManRuns { mr_x : Ind ; mr_man : man mr_x ; mr_run : run mr_x }.
Record ManWalks := mkManWalks { mw_x : Ind ; mw_man : man mw_x ; mw_walk : walk mw_x }.
Record IndOnly := mkIndOnly { io_x : Ind }.

(** Coercions for subtyping *)
Definition ManRuns_to_IndOnly (m : ManRuns) : IndOnly := mkIndOnly (mr_x m).
Coercion ManRuns_to_IndOnly : ManRuns >-> IndOnly.
Definition ManRuns_to_Ind (m : ManRuns) : Ind := mr_x m.
Coercion ManRuns_to_Ind : ManRuns >-> Ind.


(** ============================================================ *)
(** PART A: Parallel theorems — same results as deep version     *)
(** ============================================================ *)

Section ParallelTheorems.

  (** --- A1: Basic inference: "Every man runs. John is a man. John runs." --- *)

  Hypothesis every_man_runs : forall x : Ind, man x -> run x.
  Hypothesis john_is_man : man john.

  Theorem shallow_john_runs : run john.
  Proof. apply every_man_runs. exact john_is_man. Qed.

  (** COMPARE with deep version:
      Deep:    apply every_man_runs. exact john_is_man.
      Shallow: apply every_man_runs. exact john_is_man.
      IDENTICAL proof structure. But note:
      - Deep needs a model parameter M everywhere
      - Deep works at the level of m_ptype_assign, not Prop
      - Shallow is just Coq's native logic *)


  (** --- A2: Record type subtyping (width) ---
      ManRuns <: IndOnly because ManRuns has all fields of IndOnly (and more). *)

  Theorem shallow_width_subtyping : forall m : ManRuns, exists i : IndOnly, True.
  Proof. intros. exists (ManRuns_to_IndOnly m). exact I. Qed.

  (** More directly via coercion: *)
  Theorem shallow_width_subtyping_2 : forall (m : ManRuns) (P : Ind -> Prop),
    P (mr_x m) -> P m.
  Proof. intros. exact H. Qed.

  (** COMPARE with deep version:
      Deep needed inversion on witnesses_rt, explicit field matching.
      Shallow: coercion handles it automatically. CLEANER. *)


  (** --- A3: Meet is a subtype of both conjuncts --- *)

  (** In shallow, meet = product type *)
  Theorem shallow_meet_sub_l : forall (A B : Prop), A /\ B -> A.
  Proof. intros. destruct H. exact H. Qed.

  Theorem shallow_meet_sub_r : forall (A B : Prop), A /\ B -> B.
  Proof. intros. destruct H. exact H0. Qed.


  (** --- A4: Join is a supertype of both disjuncts --- *)

  Theorem shallow_join_sup_l : forall (A B : Prop), A -> A \/ B.
  Proof. intros. left. exact H. Qed.

  Theorem shallow_join_sup_r : forall (A B : Prop), B -> A \/ B.
  Proof. intros. right. exact H. Qed.


  (** --- A5: Singleton subtyping ---
      If x = john and man(x), then man(john). *)

  Theorem shallow_singleton_sub : forall (x : Ind),
    x = john -> man x -> man john.
  Proof. intros. rewrite <- H. exact H0. Qed.


  (** --- A6: Transitivity of subtyping --- *)

  (** In shallow, subtyping = implication between types (via coercions).
      Transitivity is just function composition. *)
  Theorem shallow_sub_trans : forall (A B C : Prop),
    (A -> B) -> (B -> C) -> (A -> C).
  Proof. intros. apply H0. apply H. exact H1. Qed.

End ParallelTheorems.


(** ============================================================ *)
(** PART B: Where shallow is CLEANER than deep                   *)
(** ============================================================ *)

(** --- B1: Dependent record types with real computation ---
    Coq type-checks the dependency directly. *)

Section ShallowCleaner.

  (** "Every man who runs also walks" — complex inference *)
  Hypothesis man_run_walk : forall x : Ind, man x -> run x -> walk x.

  (** Given a witness of ManRuns, construct a witness of ManWalks *)
  Theorem shallow_complex_inference : forall (m : ManRuns),
    walk (mr_x m).
  Proof.
    intros. apply man_run_walk.
    - exact (mr_man m).
    - exact (mr_run m).
  Qed.

  (** COMPARE with deep: would need to deconstruct the record-as-Val,
      look up each field, extract witnesses, thread the model parameter.
      Much more verbose. *)


  (** --- B2: Quantification is native --- *)

  (** "Some man runs" — existential *)
  Hypothesis some_man_runs : exists x : Ind, man x /\ run x.

  Theorem shallow_some_man_runs_witness : exists m : ManRuns, True.
  Proof.
    destruct some_man_runs as [x [Hm Hr]].
    exists (mkManRuns x Hm Hr). exact I.
  Qed.

  (** In deep: existential quantification is over Val, need to
      construct LabelledSet records manually, verify witness relation. *)


  (** --- B3: Type-level safety ---
      The shallow embedding catches errors at compile time that
      the deep embedding misses. *)

  (** This would be a type error in the shallow embedding:
      Definition bad : ManRuns := mkManRuns john ??? ???
      We can't construct a ManRuns without proofs of man(john) and run(john).

      In the deep embedding, we could construct:
      VLSet (ls_pair "x" (VStr "john") "c_man" (VNat 42))
      and it would parse fine — the error only shows up when we
      try to prove the witnesses_rt relation. *)

End ShallowCleaner.


(** ============================================================ *)
(** PART C: Things the shallow embedding CANNOT do               *)
(** These are marked Abort or use comments to explain the gap.   *)
(** ============================================================ *)

(** --- C1: Types as values ---
    Cannot store a Coq type inside a record field. *)

(* This is ILLEGAL in Coq:
   Record InfoState := mkInfoState {
     content : Ind ;
     content_type : Set    (* Set lives in Type, not Set *)
   }.
   The "content_type" field would need to be in Type, making
   the whole record live in Type — breaking the universe.

   DEEP equivalent works fine:
   VLSet (ls_pair "content" (VStr "john") "type" (VType (TBasic "Ind")))
*)


(** --- C2: Merge of record types ---
    Cannot compute a new Record type from two existing ones. *)

(* IMPOSSIBLE to define:
   Definition merge_rt (T1 T2 : Set) : Set := ???
   There is no Coq function that takes two Record types and
   returns a new Record type combining their fields.

   DEEP equivalent is a simple list append:
   rt_merge_simple rt1 rt2
*)


(** --- C3: Relabelling ---
    ManRuns and the structurally identical record type with
    different field names are DIFFERENT types in Coq. *)

Record AgentRuns := mkAgentRuns {
  ar_agent : Ind ;
  ar_man   : man ar_agent ;
  ar_run   : run ar_agent
}.

(** ManRuns and AgentRuns have identical field types but different
    field names. There is NO WAY to prove they are isomorphic
    automatically — we must write the isomorphism by hand. *)

Definition ManRuns_to_AgentRuns (m : ManRuns) : AgentRuns :=
  mkAgentRuns (mr_x m) (mr_man m) (mr_run m).

Definition AgentRuns_to_ManRuns (a : AgentRuns) : ManRuns :=
  mkManRuns (ar_agent a) (ar_man a) (ar_run a).

(** We can prove these are inverses, but we had to write them
    manually. In the deep embedding, a relabelling function
    handles this generically for ANY pair of record types. *)

Theorem shallow_relabel_roundtrip : forall m : ManRuns,
  AgentRuns_to_ManRuns (ManRuns_to_AgentRuns m) = m.
Proof. intros. destruct m. reflexivity. Qed.


(** --- C4: Reasoning about empty types ---
    In shallow Coq, we cannot prove a type is uninhabited
    without extra axioms or contradictions. *)

Parameter Unicorn : Set.

(* We CANNOT prove: ~ exists u : Unicorn, True.
   Because Coq is consistent — it won't let us prove
   a type is empty unless we derive a contradiction.

   In deep: we just say m_basic_assign M "Unicorn" a -> False
   for all a in model M, and the proof goes through trivially.
   The type TBasic "Unicorn" still exists as a value. *)


(** --- C5: Cross-model reasoning ---
    The shallow embedding has no model parameter.
    We cannot express "this type is inhabited in model M1
    but not in model M2." *)

(* IMPOSSIBLE in shallow:
   "Dragon is possible but not necessary"
   would require: exists M, inhabited_in M Dragon
              and: exists M, ~ inhabited_in M Dragon
   But there is no M parameter to quantify over.

   DEEP version proves this directly (see TTR_theorems_deep.v, B6). *)


(** --- C6: Dynamic type construction ---
    Cannot create new types at "runtime" in response to data. *)

(* In dialogue:
   "There's a dog. It's barking."
   The second sentence creates a singleton type for THAT specific dog.

   In deep: we can compute TSingleton (TBasic "Dog") (VStr "fido")
   from runtime data.

   In shallow: we would need to define a new Coq type for each
   discourse referent AT COMPILE TIME. Types cannot be computed
   from values in Coq's native type system.
   (Coq's universe polymorphism and dependent types can simulate
    some of this, but not the full generality Cooper needs.) *)
