(* ========================================================================== *)
(*  DTS.v — Dependent Type Semantics (Bekki), the dynamic branch from Ranta   *)
(*  FORMAL-ATLAS / atlas/mtt_ranta                                            *)
(* ========================================================================== *)
(*
   SOURCES
     [B14]  Bekki, D. (2014). Representing anaphora with dependent types.
       LACL 2014, LNCS 8535.  [the @-operator (underspecified term) and
       anaphora resolution as type checking / proof search]
     [BM17] Bekki, D. & Mineshima, K. (2017). Context-passing and
       underspecification in Dependent Type Semantics.  In
       Chatzikyriakidis & Luo (eds), Modern Perspectives in
       Type-Theoretical Semantics, Springer.  [presupposition as
       @-terms; projection through local contexts; felicity conditions]
     SOURCE CHECK 2026-09-12: BM17 read on disk (the PDF filename is
     Bekki_Mineshima_2017_CalculatingProjectionsViaTypeChecking.pdf,
     but its actual title is the one above).  Section 1.4 pp. 17-19
     explicitly uses CN predicates over entity, unlike Ranta/MTT.
     PredicateDTS below implements that ontology and its explicit
     re-encoding into Ranta's sorted contexts.  B14 remains unavailable.
   Companions: atlas/mtt_ranta/Ranta.v (this file Requires it — DTS is
   the dynamic development OF Ranta's programme; the bridge theorems
   live here), atlas/mtt_ranta/MTT.v (the lexical branch; see
   edges/ranta__dts.json and the region record).

   WHAT IS FORMALIZED
     PredicateDTS (source-aligned core): predicate CNs over entity,
       evidence-bearing donkey context, resolutions, an explicit
       context isomorphism to induced Sigma noun types, and the
       translated canonical reading.  Dynamic conjunction retains the
       old context alongside the new discourse witness (BM17 Def. 4).
     Parts 1-3 below are retained as SORTED SPECIALIZATIONS / helpers:
       their direct Ranta equations do not establish that DTS and
       Ranta start with identical noun ontologies.
     Part 1  Underspecification: an @-slot of type A against a context
             Ctx is a RESOLUTION SPACE Ctx -> A; a sentence with n
             anaphors denotes a function from resolutions to meanings
             (B14's @-operators, shallowly).  Felicity = inhabitedness
             of the resolution space (type checking succeeds).
     Part 2  The donkey discourse in DTS: the conditional's antecedent
             is the Sigma-context; the consequent's pronouns are @-slots
             over it; theorems:
             - dts_donkey_canonical: the projection resolution recovers
               EXACTLY Ranta's donkey_sentence (definitional) — DTS
               resolution GENERALIZES Ranta's pronominalization rule;
             - dts_donkey_felicitous: the resolution space is inhabited
               (the felicity condition holds);
             - resolution_ambiguity: in a two-antecedent discourse the
               resolution space contains extensionally distinct
               resolvents — ambiguity = multiplicity of resolutions.
     Part 3  Presupposition (BM17): "the N" is an @-slot; theorems:
             - the_bare_presupposes: in the empty context, resolving
               "the farmer talks" is (up to iso) EXHIBITING a farmer —
               the presupposition demands a witness;
             - the_conditional_projects_nothing: inside the donkey
               conditional the same @-slot resolves LOCALLY from the
               antecedent, so the whole conditional's resolution space
               is inhabited unconditionally — presupposition projection
               computed by context passing.

   COMPANION ADDED 2026-09-13
     DTS_Resolution.v implements a bounded object-language @ calculus:
     entity-projection terms in dependent telescopes, declared hole typing,
     consistent substitution, finite search and source-context reassociation.
     The limits below concern THIS shallow file or the full DTS calculus;
     they do not deny the new companion's restricted search implementation.

   NOT FORMALIZED (and why)
     * B14's syntax-semantics interface (CCG derivations, the lightblue
       parser): out of scope; the fragment route is in Ranta.v Part 5.
     * The @-operator as a deep object-language term-former with its
       typing/search rules: not implemented here; @-slots are rendered
       as lambda-abstracted resolution parameters (ARTIFACT below).
       A deep calculus could be represented in Coq; its absence here
       is a scope choice, not a foundational impossibility.
     * Proof search itself (resolution is EXHIBITED, not searched):
       the felicity theorems provide the witnesses that Bekki's type
       checker would find.
     * Selectional restrictions on resolution (gender/number features).

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-i]   B14's @_i : A is a term whose typing obligation is
                    discharged by proof search.  Shallowly, a meaning
                    with an @-slot is a FUNCTION over the resolution
                    space (Ctx -> A) -> Meaning; underspecification
                    becomes parameterization, resolution becomes
                    application. This omits typed object syntax and the
                    checking/search discipline, not just execution order.
                    See the companion for the explicitly bounded repair.
     [ARTIFACT-ii]  Felicity ("the sentence type checks") is rendered as
                    inhabitedness of the resolution space — proved by
                    exhibiting the resolvent Bekki's checker would
                    construct.
     [ARTIFACT-iv]  Zero axioms; contexts and lexica are Section
                    variables, countermodels concrete Inductives.
*)

Require mtt_ranta.Ranta.

(* ========================================================================== *)
(*  Part 1 — Underspecification and resolution                                *)
(* ========================================================================== *)

(* The resolution space of an @-slot of type A against context Ctx
   (B14: the @-term's typing obligation Ctx |- @ : A). *)
Definition resolution (Ctx A : Type) : Type := Ctx -> A.

(* Felicity: the obligation is dischargeable (ARTIFACT-ii). *)
Definition felicitous (Ctx A : Type) : Type := resolution Ctx A.

(* ========================================================================== *)
(*  Part 2 — The donkey discourse                                             *)
(* ========================================================================== *)

Section Donkey.

Variables (Farmer Donkey : Type).
Variables (own beat : Farmer -> Donkey -> Type).

(* The antecedent context, exactly Ranta's (Ranta.v Part 3). *)
Definition ante : Type := {x : Farmer & {y : Donkey & own x y}}.

(* The DTS meaning of "if a farmer owns a donkey, he beats it": the
   pronouns are @-slots resolved against the antecedent context — the
   meaning is a function of the two resolutions (ARTIFACT-i). *)
Definition dts_donkey
  (he : resolution ante Farmer) (it : resolution ante Donkey) : Type :=
  forall u : ante, beat (he u) (it u).

(* DTS-1.  THE bridge theorem: the canonical (projection) resolution
   recovers Ranta's donkey sentence DEFINITIONALLY — B14's resolution
   generalizes R95 §4.2's pronominalization rule, which picks exactly
   these projections. *)
Theorem dts_donkey_canonical :
  dts_donkey (fun u => projT1 u) (fun u => projT1 (projT2 u))
  = Ranta.donkey_sentence Farmer Donkey own beat.
Proof. reflexivity. Qed.

(* DTS-2.  Felicity: the resolution spaces are inhabited — the typing
   obligations of both @-slots are dischargeable (what Bekki's type
   checker searches for, exhibited). *)
Theorem dts_donkey_felicitous :
  felicitous ante Farmer * felicitous ante Donkey.
Proof.
  split.
  - exact (fun u => projT1 u).
  - exact (fun u => projT1 (projT2 u)).
Qed.

(* DTS-3.  The strong reading, inherited through the canonical
   resolution (Ranta.donkey_curry across the bridge). *)
Theorem dts_donkey_strong :
  Ranta.tequiv
    (dts_donkey (fun u => projT1 u) (fun u => projT1 (projT2 u)))
    (forall (x : Farmer) (y : Donkey), own x y -> beat x y).
Proof.
  rewrite dts_donkey_canonical.
  exact (Ranta.donkey_curry Farmer Donkey own beat).
Qed.

End Donkey.

(* Ambiguity = multiplicity of resolutions: a discourse with two Farmer
   antecedents ("a farmer meets a farmer; he talks") has extensionally
   distinct resolvents for "he" — concretely, over bool. *)
Theorem resolution_ambiguity :
  exists (Farmer : Type) (meet : Farmer -> Farmer -> Type)
         (Ctx : Type)
         (r1 r2 : resolution Ctx Farmer) (c : Ctx),
    r1 c <> r2 c.
Proof.
  exists bool, (fun _ _ => unit).
  exists {x : bool & {y : bool & unit}}.
  exists (fun u : {x : bool & {y : bool & unit}} => projT1 u),
         (fun u : {x : bool & {y : bool & unit}} => projT1 (projT2 u)).
  exists (existT _ true (existT _ false tt)).
  simpl; intros H; discriminate H.
Qed.

(* ========================================================================== *)
(*  Part 3 — Presupposition as @-terms (BM17)                                 *)
(* ========================================================================== *)

Section Presupposition.

Variables (Farmer Donkey : Type).
Variables (own beat : Farmer -> Donkey -> Type) (talk : Farmer -> Type).

(* "The farmer talks", uttered in a context Ctx: the definite is an
   @-slot of type Farmer. *)
Definition the_farmer_talks (Ctx : Type)
  (the : resolution Ctx Farmer) : Type :=
  forall c : Ctx, talk (the c).

(* DTS-4.  In the EMPTY context (unit), discharging the definite's
   obligation is — up to equivalence — exhibiting a farmer: the
   presupposition demands a global witness (BM17's accommodation
   datum). *)
Theorem the_bare_presupposes :
  Ranta.tequiv (felicitous unit Farmer) Farmer.
Proof.
  split.
  - intros r; exact (r tt).
  - intros f _; exact f.
Qed.

(* DTS-5.  Inside the donkey conditional, the same @-slot resolves
   LOCALLY from the antecedent context, so the conditional as a whole
   carries no farmer-presupposition: its resolution space is inhabited
   UNCONDITIONALLY — presupposition projection computed by context
   passing (BM17). *)
Theorem the_conditional_projects_nothing :
  felicitous (ante Farmer Donkey own) Farmer.
Proof. exact (fun u => projT1 u). Qed.

(* ... and with that local resolution the conditional reading is again
   Ranta's donkey sentence: "if a farmer owns a donkey, THE FARMER beats
   it" = the pronominal version (definitional). *)
Theorem the_conditional_is_donkey :
  (forall u : ante Farmer Donkey own,
     beat ((fun v => projT1 v) u) (projT1 (projT2 u)))
  = Ranta.donkey_sentence Farmer Donkey own beat.
Proof. reflexivity. Qed.

End Presupposition.

(* ====================================================================== *)
(* BM17 section 1.4, pp. 17-19: predicate CNs, not primitive noun sorts.    *)
(* ====================================================================== *)
Module PredicateDTS.
Section Nouns.
Variable Entity : Type.
Variables farmer donkey : Entity -> Type.
Variables own beat : Entity -> Entity -> Type.

Definition farmer_type : Type := {x : Entity & farmer x}.
Definition donkey_type : Type := {y : Entity & donkey y}.

(* BM17 (7): each individual carries its noun-predicate evidence. *)
Definition context : Type :=
  {x : Entity & (farmer x *
    {y : Entity & (donkey y * own x y)%type})%type}.
Definition subject (u : context) : Entity := projT1 u.
Definition object (u : context) : Entity := projT1 (snd (projT2 u)).

Definition meaning (he it : resolution context Entity) : Type :=
  forall u : context, beat (he u) (it u).
Definition canonical : Type := meaning subject object.

Definition sorted_context : Type :=
  Ranta.donkey_ctx farmer_type donkey_type
    (fun x y => own (projT1 x) (projT1 y)).

Definition to_sorted (u : context) : sorted_context :=
  match u with
  | existT _ x (fx, existT _ y (dy, oxy)) =>
      existT _ (existT _ x fx) (existT _ (existT _ y dy) oxy)
  end.

Definition from_sorted (s : sorted_context) : context :=
  match s with
  | existT _ (existT _ x fx) (existT _ (existT _ y dy) oxy) =>
      existT _ x (fx, existT _ y (dy, oxy))
  end.

Theorem context_roundtrip : forall u, from_sorted (to_sorted u) = u.
Proof. intros [x [fx [y [dy oxy]]]]; reflexivity. Qed.

Theorem sorted_roundtrip : forall s, to_sorted (from_sorted s) = s.
Proof. intros [[x fx] [[y dy] oxy]]; reflexivity. Qed.

(* The comparison requires induced noun types and these two maps. *)
Theorem canonical_ranta_translation :
  Ranta.tequiv canonical
    (Ranta.donkey_sentence farmer_type donkey_type
      (fun x y => own (projT1 x) (projT1 y))
      (fun x y => beat (projT1 x) (projT1 y))).
Proof.
  split.
  - intros H [[x fx] [[y dy] oxy]].
    exact (H (existT _ x (fx, existT _ y (dy, oxy)))).
  - intros H [x [fx [y [dy oxy]]]].
    exact (H (existT _ (existT _ x fx) (existT _ (existT _ y dy) oxy))).
Qed.

Theorem canonical_strong_reading :
  Ranta.tequiv canonical
    (forall x, farmer x -> forall y, donkey y -> own x y -> beat x y).
Proof.
  split.
  - intros H x fx y dy oxy; exact (H (existT _ x (fx, existT _ y (dy, oxy)))).
  - intros H [x [fx [y [dy oxy]]]]; exact (H x fx y dy oxy).
Qed.
End Nouns.

(* BM17 section 3.1 Definition 4, p. 24: N receives (old context,
   proof of M), so earlier discourse referents remain accessible. *)
Definition extend (Ctx : Type) (P : Ctx -> Type) : Type := {c : Ctx & P c}.
Definition dynamic_and (Ctx : Type) (P : Ctx -> Type)
  (Q : extend Ctx P -> Type) (c : Ctx) : Type :=
  {p : P c & Q (existT P c p)}.

Definition dependent_resolution (Ctx : Type) (A : Ctx -> Type) : Type :=
  forall c : Ctx, A c.

Section Discourse.
Variables Ctx Entity : Type.
Variables man enter whistle : Entity -> Type.
Definition first : Type := {x : Entity & (man x * enter x)%type}.
Definition sequence (c : Ctx) : Type :=
  dynamic_and Ctx (fun _ => first)
    (fun history => whistle (projT1 (projT2 history))) c.

(* BM17 (18): the discourse retains the first assertion and supplies
   the same individual to the second.  No anaphor search is claimed. *)
Theorem discourse_content : forall c,
  Ranta.tequiv (sequence c)
    {x : Entity & (man x * (enter x * whistle x))%type}.
Proof.
  intros c; split.
  - intros [[x [Hm He]] Hw]; exists x; exact (Hm, (He, Hw)).
  - intros [x [Hm [He Hw]]]; exists (existT _ x (Hm, He)); exact Hw.
Qed.
End Discourse.
End PredicateDTS.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)
(* Output under Coq 8.20.1 (2026-09-05): every theorem below prints
   "Closed under the global context" (ARTIFACT-iv). *)
Print Assumptions dts_donkey_canonical.
Print Assumptions dts_donkey_felicitous.
Print Assumptions dts_donkey_strong.
Print Assumptions resolution_ambiguity.
Print Assumptions the_bare_presupposes.
Print Assumptions the_conditional_projects_nothing.
Print Assumptions the_conditional_is_donkey.
Print Assumptions PredicateDTS.context_roundtrip.
Print Assumptions PredicateDTS.sorted_roundtrip.
Print Assumptions PredicateDTS.canonical_ranta_translation.
Print Assumptions PredicateDTS.canonical_strong_reading.
Print Assumptions PredicateDTS.discourse_content.
