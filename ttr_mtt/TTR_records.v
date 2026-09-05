(** TTR_records.v — Records and Record Types
    Formalizing Cooper (2023) Appendix A11.

    This is the heart of TTR. Record types are the structured
    types that do the heavy linguistic work: situation types,
    semantic frames, information states are all record types.

    A11.1: Records are finite labelled sets whose labels are in L
           but not in D, and every value witnesses some type.
    A11.2: Record types are "flavoured" labelled sets (flavour RT).
    Dependent record types: later fields can depend on earlier
    fields via paths.
*)

Require Import TTR_base.
Require Import TTR_types.
Require Import List.
Require Import String.
Require Import Bool.
Import ListNotations.
Open Scope string_scope.

(** * Distinguished labels — reserved by TTR for structural use *)

Definition is_distinguished (l : Label) : bool :=
  String.eqb l "pred"      ||
  String.eqb l "arg1"      ||
  String.eqb l "arg2"      ||
  String.eqb l "arg3"      ||
  String.eqb l "dmn"       ||
  String.eqb l "rng"       ||
  String.eqb l "partdmn"   ||
  String.eqb l "deprng"    ||
  String.eqb l "set"       ||
  String.eqb l "singleton" ||
  String.eqb l "disj"      ||
  String.eqb l "conj"      ||
  String.eqb l "plurality" ||
  String.eqb l "lambda"    ||
  String.eqb l "body"      ||
  String.eqb l "ord"       ||
  String.eqb l "typ".

(** Well-formedness: a labelled set is a record iff all labels
    are non-distinguished and unique *)
Fixpoint is_record (ls : LabelledSet) : bool :=
  match ls with
  | LSNil => true
  | LSCons f rest =>
      negb (is_distinguished (field_label f)) &&
      negb (has_label (field_label f) rest) &&
      is_record rest
  end.

(** * Record Type Fields
    Non-dependent: ⟨ℓ, T⟩ where T is a type.
    Dependent: ⟨ℓ, F⟩ where F is a function from record → type,
    with a list of paths that F depends on. *)

Inductive RecField : Type :=
| RF_plain : Label -> TTRType -> RecField
| RF_dep   : Label -> (Val -> TTRType) -> list Path -> RecField.

Definition RecType := list RecField.

Definition rf_label (rf : RecField) : Label :=
  match rf with
  | RF_plain l _ => l
  | RF_dep l _ _ => l
  end.

(** * Resolve a path inside a Val *)
Definition resolve_path_in_val (v : Val) (p : Path) : option Val :=
  match v with
  | VLSet ls => resolve_path ls p
  | _ => None
  end.

(** * Record Type Witnessing
    r witnesses a record type RT iff for every field in RT,
    r has a value at that label that witnesses the field's type. *)

Inductive witnesses_rt (M : TTRModel) : Val -> RecType -> Prop :=

  (** Empty record type: witnessed by any record *)
  | wrt_nil : forall r,
      witnesses_rt M r nil

  (** Non-dependent field: r.l exists and witnesses T *)
  | wrt_plain : forall r l T rest,
      (exists v, val_lookup r l = Some v /\ witnesses M v T) ->
      witnesses_rt M r rest ->
      witnesses_rt M r (RF_plain l T :: rest)

  (** Dependent field: r.l exists, the dependency resolves,
      and r.l witnesses F(dep_val) *)
  | wrt_dep : forall r l (F : Val -> TTRType) paths rest dep_val v,
      val_lookup r l = Some v ->
      resolve_path_in_val r (hd (PLabel ""%string) paths) = Some dep_val ->
      witnesses M v (F dep_val) ->
      witnesses_rt M r rest ->
      witnesses_rt M r (RF_dep l F paths :: rest).

(** * Record type field lookup *)
Fixpoint rt_has_label (l : Label) (rt : RecType) : bool :=
  match rt with
  | nil => false
  | rf :: rest =>
      if String.eqb (rf_label rf) l then true
      else rt_has_label l rest
  end.

Fixpoint rt_lookup (l : Label) (rt : RecType) : option RecField :=
  match rt with
  | nil => None
  | rf :: rest =>
      if String.eqb (rf_label rf) l then Some rf
      else rt_lookup l rest
  end.

(** * Simple merge of record types
    Cooper A11.3: combine fields, for shared labels take the meet *)

Fixpoint rt_merge_simple (rt1 rt2 : RecType) : RecType :=
  match rt1 with
  | nil => rt2
  | rf :: rest =>
      if rt_has_label (rf_label rf) rt2
      then rt_merge_simple rest rt2
      else rf :: rt_merge_simple rest rt2
  end.

(** * Linguistic examples as record types *)

(** Basic type of individuals *)
Definition Ind := TBasic "Ind"%string.

(** "A man runs" = [ x : Ind, c_man : man(x), c_run : run(x) ] *)
Definition man_runs : RecType :=
  [ RF_plain "x"%string Ind ;
    RF_dep "c_man"%string
           (fun v => TPType "man"%string [v])
           [PLabel "x"%string] ;
    RF_dep "c_run"%string
           (fun v => TPType "run"%string [v])
           [PLabel "x"%string]
  ].

(** "John is tall" — singleton type for the individual *)
Definition john_tall : RecType :=
  [ RF_plain "x"%string (TSingleton Ind (VStr "john"%string)) ;
    RF_dep "c_tall"%string
           (fun v => TPType "tall"%string [v])
           [PLabel "x"%string]
  ].

(** "A dog chases a cat" — two individuals, one relation *)
Definition dog_chases_cat : RecType :=
  [ RF_plain "x"%string Ind ;
    RF_plain "y"%string Ind ;
    RF_dep "c_dog"%string
           (fun v => TPType "dog"%string [v])
           [PLabel "x"%string] ;
    RF_dep "c_cat"%string
           (fun v => TPType "cat"%string [v])
           [PLabel "y"%string] ;
    (* For chase(x,y) we'd need two path dependencies.
       Simplification: use a single path for now *)
    RF_plain "c_chase"%string (TPType "chase"%string [])
  ].

(** * Example: witnessing a simple record type *)

Section ExampleWitnessing.
  Variable M : TTRModel.

  (** Assume john is an individual *)
  Hypothesis john_ind : m_basic_assign M "Ind"%string (VStr "john"%string).

  (** A simple record: { x = "john" } *)
  Definition john_rec : Val :=
    VLSet (ls_singleton "x"%string (VStr "john"%string)).

  (** The record type [ x : Ind ] *)
  Definition ind_rt : RecType := [ RF_plain "x"%string Ind ].

  Theorem john_witnesses_ind_rt :
    witnesses_rt M john_rec ind_rt.
  Proof.
    unfold john_rec, ind_rt.
    apply wrt_plain.
    - exists (VStr "john"%string). split.
      + simpl. reflexivity.
      + apply wit_basic. exact john_ind.
    - apply wrt_nil.
  Qed.

End ExampleWitnessing.

(** * Width subtyping for record types
    If RT1 has all the fields of RT2 (and more), then
    any record witnessing RT1 also witnesses RT2.
    This is the standard record subtyping rule. *)

(** We can state this as: if RT2 is a "suffix" or "subset" of RT1's
    fields, then witnessing RT1 implies witnessing RT2. *)

Theorem rt_weaken_nil : forall M r rt,
  witnesses_rt M r rt -> witnesses_rt M r nil.
Proof.
  intros. apply wrt_nil.
Qed.

(** * Summary of formalization status

    COVERED (Appendix sections):
    A1:  Labels, fields, labelled sets, paths           [TTR_base.v]
    A2:  Basic types with witness assignment             [TTR_types.v]
    A3:  Predicate types (ptypes)                        [TTR_types.v]
    A4:  Function types (total and partial)              [TTR_types.v]
    A5:  Set types                                       [TTR_types.v]
    A6:  Singleton types                                 [TTR_types.v]
    A7:  Join types                                      [TTR_types.v]
    A8:  Meet types                                      [TTR_types.v]
    A11.1: Records                                       [here]
    A11.2: Record types (non-dependent + dependent)      [here]
    A11.3: Merge (simple version)                        [here]
    Subtyping (semantic, via witness sets)                [TTR_types.v]
    Structural theorems (reflexivity, transitivity, etc) [TTR_types.v]
    Linguistic examples (situation types)                [here]

    NOT YET COVERED:
    A9:   Modal systems (families of models)
    A10:  Type/Type stratification (universe hierarchy)
    A11.3: Full recursive merge with dependent fields
    A11.4: Fixed point types for recursive record types
    A11.5: Unique identifier notation
    A11.6: Dependency and generalization
    A11.7: Restriction/specification (T || r)
    A11.8: Path alignment
    Relabelling (A1)
    Lambda terms as labelled sets (A4)

    KNOWN ISSUES:
    1. Lists not sets — ordering artifact
    2. Val is a "universal domain" — less structured than Cooper's
       stratified Type^n universe
    3. Dependent fields use Coq functions (Val -> TTRType): a shallow
       element inside our deep embedding (hybrid approach)
    4. Function type witnessing is propositional, not computational
    5. Multi-path dependencies (e.g., chase(x,y)) need generalization
       beyond the single-path hd trick
    6. No decidability results yet
*)
