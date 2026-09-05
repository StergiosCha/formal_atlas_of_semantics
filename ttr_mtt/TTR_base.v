(** TTR_base.v — Foundations: Labels, Fields, Labelled Sets, Paths
    Formalizing Cooper (2023) Appendix A1: Underlying set theory.

    Deep embedding approach: TTR's set-theoretic substrate is
    represented as Coq inductive types. We use lists of pairs
    rather than actual sets, accepting the ordering artifact.

    Design note: Cooper assumes ZF with urelements. We use Coq's
    native types as the "universe of urelements" and represent
    labelled sets as association lists. This is a pragmatic choice —
    it loses the extensionality of sets (two lists with the same
    elements in different order are not definitionally equal) but
    gains decidability and computability.
*)

Require Import List.
Require Import String.
Require Import Arith.
Require Import Bool.
Import ListNotations.

(** * Labels
    Cooper A1: "among the urelements is a countably infinite set
    which is designated as the set of labels."
    We use strings as labels. *)

Definition Label := string.

(** * Flavours
    Cooper A1: "among the urelements there is a finite or countably
    infinite set, disjoint from the set of labels, designated as
    the set of flavours."
    We use an inductive type. RT is the record-type flavour (A11). *)

Inductive Flavour : Set :=
| Plain    (* unflavoured *)
| RT       (* record type flavour, Cooper A11 *)
| Manifest (* for manifest/singleton fields *).

(** * The TTR value universe
    Everything that can appear as a value in a field.
    This is our "set of urelements + sets" — deeply embedded. *)

Inductive Val : Type :=
| VNat   : nat -> Val
| VBool  : bool -> Val
| VStr   : string -> Val
| VLabel : Label -> Val
| VPair  : Val -> Val -> Val     (* ordered pairs *)
| VLSet  : LabelledSet -> Val    (* labelled sets as values *)
| VFun   : Label -> Val -> Val   (* lambda abstraction placeholder *)
| VPred  : string -> list Val -> Val  (* predicate application *)
| VType  : TTRType -> Val        (* types are first-class values *)

(** * Fields
    Cooper A1: "A field is either
      an ordered pair ⟨ℓ, a⟩ where ℓ is a label and a is not a label or a flavour
    or
      an ordered triple ⟨ℓ, a, i⟩ where ⟨ℓ, a⟩ is a field and i is an index."

    We simplify: a field is a label-value pair, optionally indexed. *)

with Field : Type :=
| FPair  : Label -> Val -> Field           (* ⟨ℓ, a⟩ *)
| FTriple : Label -> Val -> nat -> Field   (* ⟨ℓ, a, i⟩ flavoured/indexed *)

(** * Labelled Sets
    Cooper A1: "An (unflavoured) labelled set is a set of fields
    such that no more than one field can contain any particular
    label as its first member."

    Represented as lists of fields. The unique-label invariant
    is maintained as a separate well-formedness predicate. *)

with LabelledSet : Type :=
| LSNil  : LabelledSet
| LSCons : Field -> LabelledSet -> LabelledSet

(** * TTR Types (forward declaration for mutual recursion)
    Full definition is in TTR_types.v; here we just need
    the constructor tags for the Val type. *)

with TTRType : Type :=
| TBasic    : string -> TTRType                     (* named basic type *)
| TPType    : string -> list Val -> TTRType          (* predicate type P(a1,...,an) *)
| TFun      : TTRType -> TTRType -> TTRType          (* T1 -> T2 *)
| TPartFun  : TTRType -> TTRType -> TTRType          (* T1 ⇀ T2 *)
| TRecType  : LabelledSet -> TTRType                 (* record type *)
| TJoin     : TTRType -> TTRType -> TTRType          (* T1 ∨ T2 *)
| TMeet     : TTRType -> TTRType -> TTRType          (* T1 ∧ T2 *)
| TSet      : TTRType -> TTRType                     (* set(T) *)
| TSingleton: TTRType -> Val -> TTRType              (* T_a *)
| TPlurality: TTRType -> TTRType                     (* plurality(T) *)
| TAbsurd   : TTRType.                               (* empty/absurd type *)
(** Note: Dependent function types (a : T) → F(a) are NOT in this
    mutual inductive because (Val -> TTRType) would violate strict
    positivity. They are handled in TTR_records.v via RecField. *)

(** * Extracting labels from a labelled set *)

Definition field_label (f : Field) : Label :=
  match f with
  | FPair l _ => l
  | FTriple l _ _ => l
  end.

Definition field_value (f : Field) : Val :=
  match f with
  | FPair _ v => v
  | FTriple _ v _ => v
  end.

Fixpoint ls_to_list (ls : LabelledSet) : list Field :=
  match ls with
  | LSNil => []
  | LSCons f rest => f :: ls_to_list rest
  end.

Definition labels (ls : LabelledSet) : list Label :=
  map field_label (ls_to_list ls).

(** Well-formedness: no duplicate labels *)
Fixpoint has_label (l : Label) (ls : LabelledSet) : bool :=
  match ls with
  | LSNil => false
  | LSCons f rest =>
      if String.eqb (field_label f) l then true
      else has_label l rest
  end.

Fixpoint wf_labelled_set (ls : LabelledSet) : bool :=
  match ls with
  | LSNil => true
  | LSCons f rest =>
      negb (has_label (field_label f) rest) && wf_labelled_set rest
  end.

(** * Lookup: X.ℓ — the value at label ℓ in labelled set X *)
Fixpoint ls_lookup (ls : LabelledSet) (l : Label) : option Val :=
  match ls with
  | LSNil => None
  | LSCons f rest =>
      if String.eqb (field_label f) l then Some (field_value f)
      else ls_lookup rest l
  end.

(** * Paths
    Cooper A1: "We characterize the set of paths in a labelled set,
    paths(X), by the following inductive definition:
    1. if ℓ ∈ labels(X), then ℓ ∈ paths(X)
    2. if ℓ ∈ labels(X), X.ℓ is a labelled set and π ∈ paths(X.ℓ),
       then ℓ.π ∈ paths(X)"
*)

Inductive Path : Type :=
| PLabel : Label -> Path           (* single label *)
| PDot   : Label -> Path -> Path.  (* ℓ.π *)

(** Path membership: π ∈ paths(X) *)
Fixpoint in_paths (p : Path) (ls : LabelledSet) : bool :=
  match p with
  | PLabel l => has_label l ls
  | PDot l rest =>
      match ls_lookup ls l with
      | Some (VLSet inner) => in_paths rest inner
      | _ => false
      end
  end.

(** Resolve a path: follow the path to get the value at the end *)
Fixpoint resolve_path (ls : LabelledSet) (p : Path) : option Val :=
  match p with
  | PLabel l => ls_lookup ls l
  | PDot l rest =>
      match ls_lookup ls l with
      | Some (VLSet inner) => resolve_path inner rest
      | _ => None
      end
  end.

(** Total paths: π ∈ tpaths(X) iff π ∈ paths(X) and X.π is not a labelled set *)
Definition is_labelled_set_val (v : Val) : bool :=
  match v with
  | VLSet _ => true
  | _ => false
  end.

Definition in_tpaths (p : Path) (ls : LabelledSet) : bool :=
  in_paths p ls &&
  match resolve_path ls p with
  | Some v => negb (is_labelled_set_val v)
  | None => false
  end.

(** * Path subtraction: X ⊖ π
    Cooper A1, p. 399: removing a path from a labelled set.
    We implement the simple case (removing a label). *)

Fixpoint ls_remove (ls : LabelledSet) (l : Label) : LabelledSet :=
  match ls with
  | LSNil => LSNil
  | LSCons f rest =>
      if String.eqb (field_label f) l then rest
      else LSCons f (ls_remove rest l)
  end.

(** * Building labelled sets — convenience constructors *)

Definition ls_singleton (l : Label) (v : Val) : LabelledSet :=
  LSCons (FPair l v) LSNil.

Definition ls_pair (l1 : Label) (v1 : Val) (l2 : Label) (v2 : Val) : LabelledSet :=
  LSCons (FPair l1 v1) (LSCons (FPair l2 v2) LSNil).

Definition ls_triple (l1 : Label) (v1 : Val)
                      (l2 : Label) (v2 : Val)
                      (l3 : Label) (v3 : Val) : LabelledSet :=
  LSCons (FPair l1 v1) (LSCons (FPair l2 v2) (LSCons (FPair l3 v3) LSNil)).

(** * Initial subpaths
    Cooper A1: π1 is an initial subpath of π2 iff π1 = π2 or
    there exists π such that π2 = π1.π *)

Fixpoint is_initial_subpath (p1 p2 : Path) : bool :=
  match p1, p2 with
  | PLabel l1, PLabel l2 => String.eqb l1 l2
  | PLabel l1, PDot l2 _ => String.eqb l1 l2
  | PDot l1 rest1, PDot l2 rest2 =>
      String.eqb l1 l2 && is_initial_subpath rest1 rest2
  | PDot _ _, PLabel _ => false
  end.

(** * Example: A simple labelled set and path resolution *)
(**
    Let X = { ⟨"name", "John"⟩, ⟨"age", 30⟩ }
    Then paths(X) = {"name", "age"}
    X."name" = "John"
*)

Definition example_person : LabelledSet :=
  ls_pair "name"%string (VStr "John"%string)
          "age"%string (VNat 30).

(** Nested example:
    X = { ⟨"x", {⟨"y", 5⟩}⟩ }
    paths(X) = {"x", "x"."y"}
    X."x"."y" = 5
*)
Definition example_nested : LabelledSet :=
  ls_singleton "x"%string (VLSet (ls_singleton "y"%string (VNat 5))).

(** We can state and prove simple facts about these *)
Example ex_lookup_name :
  ls_lookup example_person "name"%string = Some (VStr "John"%string).
Proof. reflexivity. Qed.

Example ex_lookup_age :
  ls_lookup example_person "age"%string = Some (VNat 30).
Proof. reflexivity. Qed.

Example ex_nested_path :
  resolve_path example_nested (PDot "x"%string (PLabel "y"%string)) = Some (VNat 5).
Proof. reflexivity. Qed.

Example ex_wf : wf_labelled_set example_person = true.
Proof. reflexivity. Qed.
