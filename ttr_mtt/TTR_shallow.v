(** TTR_shallow.v — Shallow embedding of Cooper's TTR in Coq

    The idea: instead of representing TTR types as DATA (inductive TTRType)
    and defining a separate witness relation, we USE Coq's own type system
    to model TTR directly. TTR types ARE Coq types. TTR records ARE Coq
    records. The witness relation a :_TTR T IS Coq's own a : T.

    This is essentially what Cooper hints at (p. 397) when he says TTR
    "could be presented as having a type theoretic foundation in the
    manner of Martin-Löf type theory."

    Compare with TTR_base.v + TTR_types.v + TTR_records.v (deep embedding).
*)

Require Import String.
Require Import List.
Import ListNotations.

(** * Basic types — just Coq types *)

(** In the deep version we had:
      Definition Ind := TBasic "Ind".
    and a separate witness relation.
    In the shallow version, Ind IS a Coq type: *)

Parameter Ind : Set.       (* type of individuals *)
Parameter Prop_ : Set.     (* renameable — TTR propositions-as-types *)

(** Named individuals — directly typed *)
Parameter john mary : Ind.

(** * Predicate types (ptypes) — as dependent types

    Cooper: P(a1,...,an) is a type whose witnesses are proofs/situations
    where the predicate holds of those arguments.

    Deep version:  TPType "run" [VStr "john"]  — data, checked externally.
    Shallow version: run(john) — a Coq type, inhabited iff john runs.

    This IS propositions-as-types. Cooper's ptypes become Coq Props or Sets. *)

Parameter run : Ind -> Prop.
Parameter walk : Ind -> Prop.
Parameter man : Ind -> Prop.
Parameter woman : Ind -> Prop.
Parameter dog : Ind -> Prop.
Parameter cat : Ind -> Prop.
Parameter love : Ind -> Ind -> Prop.
Parameter chase : Ind -> Ind -> Prop.

(** * Record types — as Coq Records

    Cooper A11: record types are labelled sets of type assignments.
    [ x : Ind, c_man : man(x), c_run : run(x) ]

    In Coq, this is a dependent record where later fields depend
    on earlier ones — exactly Coq's Record mechanism. *)

(** "A man runs" *)
Record ManRuns : Set := mkManRuns {
  mr_x    : Ind ;
  mr_man  : man mr_x ;     (* dependent on mr_x! *)
  mr_run  : run mr_x       (* dependent on mr_x! *)
}.

(** "A dog chases a cat" *)
Record DogChasesCat : Set := mkDogChasesCat {
  dcc_x     : Ind ;
  dcc_y     : Ind ;
  dcc_dog   : dog dcc_x ;
  dcc_cat   : cat dcc_y ;
  dcc_chase : chase dcc_x dcc_y   (* depends on BOTH x and y *)
}.

(** "John runs" — with a singleton/manifest field *)
Record JohnRuns : Set := mkJohnRuns {
  jr_x   : Ind ;
  jr_eq  : jr_x = john ;     (* singleton type: x must be john *)
  jr_run : run jr_x
}.

(** Compare with the deep version in TTR_records.v:
    Definition man_runs : RecType :=
      [ RF_plain "x" Ind ;
        RF_dep "c_man" (fun v => TPType "man" [v]) [PLabel "x"] ;
        RF_dep "c_run" (fun v => TPType "run" [v]) [PLabel "x"] ].

    The shallow version is MUCH cleaner. The dependency is expressed
    via Coq's own dependent types — no paths, no labelled sets,
    no separate witness relation. *)

(** * Records (witnesses of record types) — just inhabitants *)

(** Suppose john is a man who runs *)
Section Example.
  Hypothesis john_man : man john.
  Hypothesis john_runs : run john.

  (** A witness of the ManRuns record type *)
  Definition john_man_runs : ManRuns :=
    mkManRuns john john_man john_runs.

  (** A witness of JohnRuns *)
  Definition john_john_runs : JohnRuns :=
    mkJohnRuns john eq_refl john_runs.
End Example.

(** * Subtyping — via coercions, exactly as in Luo's MTT

    Cooper: T1 ⊑ T2 iff {a | a : T1} ⊆ {a | a : T2}.
    For records: width subtyping — more fields is a subtype.

    In Coq: we define a projection function and declare it
    as a coercion. *)

(** ManRuns has more fields than just [ x : Ind ].
    So ManRuns is a subtype of Ind (via projection). *)
Definition ManRuns_to_Ind (m : ManRuns) : Ind := mr_x m.
Coercion ManRuns_to_Ind : ManRuns >-> Ind.

(** Now we can use a ManRuns wherever an Ind is expected *)
Section SubtypingExample.
  Variable m : ManRuns.

  (** This works because of the coercion *)
  Check (run m).  (* m is coerced from ManRuns to Ind *)
End SubtypingExample.

(** * Join types — as sum types *)

(** Cooper: T1 ∨ T2, witnessed by anything that witnesses either.
    Deep version: TJoin T1 T2, with wit_join_l / wit_join_r.
    Shallow version: just Coq's sum type. *)

Definition join (A B : Set) : Set := (A + B)%type.

(** * Meet types — as product types *)

(** Cooper: T1 ∧ T2, witnessed by anything that witnesses both.
    But note: Cooper's meet means the SAME object witnesses both types.
    Coq's product type A * B has two potentially DIFFERENT objects.

    For record types, Cooper's merge μ(T1 ∧ T2) combines fields.
    This is closer to Coq's record extension/inheritance. *)

Definition meet (A B : Set) : Set := (A * B)%type.

(** * Singleton types *)

(** Cooper A6: T_a is the type whose only witness is a, and a : T.
    Shallow: just an equality type. *)

Definition singleton (A : Set) (a : A) : Set :=
  { x : A | x = a }.

(** * Function types — Coq's own arrow *)

(** Cooper A4: T1 → T2, witnesses are functions.
    This is just Coq's -> *)

(** Quantifiers as generalized functions, exactly as in Luo *)
Definition every (A : Set) (P : A -> Prop) : Prop := forall x : A, P x.
Definition some  (A : Set) (P : A -> Prop) : Prop := exists x : A, P x.

(** "Every man runs" *)
Definition every_man_runs : Prop := every Ind (fun x => man x -> run x).

(** "Some dog chases some cat" *)
Definition some_dog_chases_cat : Prop :=
  some Ind (fun x => some Ind (fun y => dog x /\ cat y /\ chase x y)).


(** * What works well in the shallow embedding *)

(** 1. Dependent record types — perfect fit with Coq Records *)

(** 2. Subtyping via coercions — same as Luo's MTT *)

(** 3. Quantification — direct, no encoding *)

(** 4. Proofs — Coq's tactic language works directly *)

Section DirectProofs.
  Hypothesis h1 : forall x, man x -> run x.  (* every man runs *)
  Hypothesis h2 : man john.                   (* john is a man *)

  Theorem john_runs_proof : run john.
  Proof. apply h1. exact h2. Qed.

  (** Compare deep version: would need to construct witness terms
      manually and thread the model parameter everywhere. *)
End DirectProofs.


(** * What BREAKS in the shallow embedding — Cooper's features
    that have no clean Coq counterpart *)

(** === PROBLEM 1: Types are not first-class values ===

    Cooper: types ARE labelled sets. You can store a type in a record
    field, compute new types, pattern-match on types. This is essential
    for his treatment of:
    - Semantic frames (types as values in information states)
    - Dynamic type creation in dialogue
    - Relabelling (structural manipulation of types)

    In Coq: types live in Type, values live in Set. You cannot put
    a type into a record field that expects a value. You'd need
    Coq's universe polymorphism or Tarski-style universes — which
    is exactly what the deep embedding gives you.

    THIS is the main thing we lose going shallow. *)

(** === PROBLEM 2: Types without witnesses ===

    Cooper: there can be types T such that A(T) = ∅.
    "Impossible" types — no witness exists in any model.
    Used for: reference to non-existent objects, fiction,
    inconsistent belief states.

    In Coq: every type is inhabited (by construction) OR we can
    have empty types — but we can't reason about "this type
    might be empty in some models but not others" without
    the model parameter.

    The deep embedding handles this naturally via the model M. *)

(** === PROBLEM 3: Merge of record types ===

    Cooper A11.3: μ(T1 ∧ T2) merges two record types by combining
    their fields and recursively merging shared labels.

    In Coq: you cannot compute a new Record type from two existing
    ones. Record types are fixed at definition time. There is no
    "merge" operation on Coq types.

    This is a showstopper for Cooper's treatment of information
    update in dialogue, where the agent's information state
    (a record type) gets merged with new incoming information. *)

(** === PROBLEM 4: Relabelling ===

    Cooper A1: η-relabelling changes the labels in a labelled set.
    Types can be structurally identical but differ in labelling.
    Used in: anaphora resolution, belief ascription (Chapter 6).

    In Coq: record field names are fixed. You can't programmatically
    rename a field. Two records with the same structure but different
    field names are completely unrelated types. *)

(** === PROBLEM 5: Modal systems ===

    Cooper A9: TYPE_MC is a family of type systems indexed by models.
    A type can have witnesses in model M1 but not in M2.
    Used for: necessity ("T is necessary iff inhabited in all M")
    and possibility ("T is possible iff inhabited in some M").

    In Coq (shallow): there is only one "model" — the global context.
    You'd need to parameterize everything by a model, which pushes
    you back toward the deep embedding. *)


(** * The MTT comparison: What Luo gives that Cooper doesn't *)

(** Luo's MTT-semantics (shallow in Coq) and Cooper's TTR (shallow)
    would look almost identical in the core fragment:

    SAME:
    - CN as types (Parameter Man : Set  vs  Ind with man : Ind -> Prop)
    - Dependent types for semantic composition
    - Records for situations/events
    - Subtyping via coercions
    - Quantifiers as polymorphic functions

    BUT Luo's MTT has advantages Cooper lacks:

    1. DOT-TYPES for copredication:
       Cooper has no native mechanism for an entity that is
       simultaneously physical and informational (a "book" that
       is heavy AND interesting). Luo uses Sigma types:
*)

Record PhyInfo : Set := mkPhyInfo {
  phy : Ind ;
  info : Ind
}.

(** A book that is both heavy (physical) and interesting (informational) *)
Parameter heavy : Ind -> Prop.
Parameter interesting : Ind -> Prop.

Section Copredication.
  Variable b : PhyInfo.

  (** "The book is heavy and interesting" — copredication *)
  Definition book_copred : Prop :=
    heavy (phy b) /\ interesting (info b).
End Copredication.

(** Cooper would need to encode this via record types with
    two different paths to the same entity — doable but not
    as clean as Luo's Sigma-type approach.

    2. COERCIVE SUBTYPING:
       Luo's coercions give you "a man walks" directly:
       if Man <: Ind, then walk : Ind -> Prop applies to m : Man
       without explicit casting. Cooper's subtyping is semantic
       (set inclusion) and doesn't compute.

    3. CNs as TYPES, not as predicates:
       Luo: Man is a type. "a man" = some Man (fun x => ...).
       Cooper: man is a predicate on Ind. "a man" = some Ind (fun x => man x /\ ...).
       Luo's version is more type-theoretic and gets better
       mileage from Coq's type system (type-checking catches
       more errors).

    4. UNIVERSE HIERARCHY:
       Coq has Type_0 : Type_1 : Type_2 : ...
       Cooper's Type^n stratification (A10) maps onto this.
       But in the shallow embedding we get it for free.
       In the deep embedding we'd need to encode it manually. *)

(** * What Cooper gives that Luo/MTT doesn't easily *)

(** 1. TYPES WITHOUT WITNESSES:
       Cooper can have T such that A(T) = ∅ in all models.
       Used for fiction, impossible objects, failed presuppositions.
       MTT: every type must be inhabited or you use False/Empty,
       but you lose the ability to "reason about" empty types
       as first-class objects.

    2. DYNAMIC TYPE CREATION:
       In dialogue, new types get created on the fly:
       "There's a dog. It's barking."
       The "it" introduces a new singleton type for that specific dog.
       Cooper: types are values, can be constructed dynamically.
       MTT: types are static, determined at definition time.

    3. MERGE:
       Fundamental to Cooper's dialogue theory. Two information
       states (record types) get merged into one. No MTT equivalent
       that doesn't involve metaprogramming.

    4. UNDERSPECIFICATION:
       Cooper (Ch. 8): a type can be underspecified — multiple
       witnesses possible, narrowed down as information accrues.
       Natural in the set-theoretic framework. In MTT you'd need
       to use refinement types or proof-irrelevant propositions.

    5. TYPES AS COGNITIVE OBJECTS:
       Cooper's entire programme is about types as things agents
       MANIPULATE — perceive, create, communicate. This requires
       types to be first-class runtime values. In Coq, types and
       values are in different universes. The deep embedding
       captures this; the shallow one cannot. *)
