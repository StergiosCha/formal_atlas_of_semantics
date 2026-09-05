(* ========================================================================== *)
(*  PTQ.v — Montague 1973, The Proper Treatment of Quantification (trunk)     *)
(*  FORMAL-ATLAS / atlas/montague                                             *)
(* ========================================================================== *)
(*
   SOURCES
     [M73] Montague, R. (1973). The proper treatment of quantification in
       ordinary English.  In Hintikka et al. (eds), Approaches to Natural
       Language, 221-242; repr. in Thomason (ed.), Formal Philosophy.
       [the type system and intension/extension operators; T2 (term
       phrases), T4 (subject-predicate), T14 (quantifying in); the
       meaning postulates for extensional verbs; the seek/find contrast]
     [DWP81] Dowty, Wall & Peters (1981). Introduction to Montague
       Semantics.  [ch. 7 exposition of PTQ used for cross-checking;
       papers/foundations/Dowty_Wall_Peters_1981_*.pdf]
   Design document: formalizing_formal_semantics/atlas/designs/
   montague_lineage.md.  This file is the TRUNK of the Montague lineage:
   the edges (PTQ_vs_Lambek.v, PTQ_vs_MTT.v, edges/ptq__*.json) grade how
   descendants build on or diverge from it.
   The older shallow/PTQ.v (972 lines, Parameter/Axiom-based, richer
   tense fragment) remains as raw material; THIS file is the zero-axiom
   canonical statement of the core.

   WHAT IS FORMALIZED
     Part 1  IL types, shallowly: e = Entity, t = Prop, <a,b> = A -> B,
             <s,a> = Index -> A; intension/extension.
     Part 2  Term phrases as generalized quantifiers: john* = fun P => P
             john (T2 type raising); the determiners every/a/no; the PTQ
             sentences "every man walks", "a man walks".
     Part 3  Quantifying-in (T14): the two scopings of "every man loves
             a woman"; the scope entailment (inverse => surface).
     Part 4  Intensionality: seek takes a QUANTIFIER argument (de
             dicto); find is the extensional lift of a first-order
             relation (the meaning-postulate shape); theorems: find
             collapses de dicto/de re; de dicto seek carries NO
             existential commitment (existence countermodel); de re
             does.
     Part 5  Barwise & Cooper hooks: PTQ's determiners are conservative
             and monotone (the evidence base for edges/
             ptq__barwise_cooper.json).
     Part 6  The modal layer, minimal: box = universal quantification
             over indices; K and Nec — the hook for edges/ptq__kratzer
             (shallow/kratzer2.v proves kratzer_must over the empty
             conversational background = this box).

   NOT FORMALIZED (and why)
     * Montague's full <A,I,J,<=,F>: the Time coordinate and tense
       operators W/H are folded into the abstract Index (the richer
       treatment lives in shallow/PTQ.v); no temporal theorems here.
     * The syntactic algebra and analysis trees (deep syntax): the
       lineage edges compare MEANINGS; the deep syntax of PTQ is in
       shallow/PTQ.v and the categorial route in Lambek.v.
     * Individual concepts (<s,e> subjects): extensionalized, as in
       most of the PTQ literature after Bennett; noted per theorem.
     * be, necessity in object position, the full T1-T17 rule list.

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-i]   Shallow IL: Coq's -> and Prop stand for <a,b> and t;
                    the intension operator is a function space over an
                    abstract Index.  IL's ^ and v are ordinary lambda
                    and application, so the ^v-cancellation laws are
                    definitional and not stated.
     [ARTIFACT-ii]  NPs are extensional GQs ((e->t)->t), not
                    <<s,<e,t>>,t>: intensionality is kept exactly where
                    PTQ's data need it (the object of seek), following
                    the Bennett-style extensionalization; the de
                    dicto/de re contrast survives intact (Part 4).
     [ARTIFACT-iv]  Zero axioms; domains and lexicon are Section
                    variables; countermodels are concrete Inductives.
*)

Definition GQ (Entity : Type) : Type := (Entity -> Prop) -> Prop.

Section PTQ.

Variables (Entity : Type) (Index : Type).

(* ========================================================================== *)
(*  Part 1 — IL types, intension and extension (M73 pp. 256-258)              *)
(* ========================================================================== *)

Definition Intension (A : Type) : Type := Index -> A.
Definition extension {A : Type} (a : Intension A) (i : Index) : A := a i.

(* ========================================================================== *)
(*  Part 2 — Term phrases as generalized quantifiers (M73 T2, T4)             *)
(* ========================================================================== *)

(* T2: proper names denote the set of their properties — type raising. *)
Definition star (j : Entity) : GQ Entity := fun P => P j.

(* The PTQ determiners (extensionalized, ARTIFACT-ii). *)
Definition d_every (N P : Entity -> Prop) : Prop := forall x, N x -> P x.
Definition d_a     (N P : Entity -> Prop) : Prop := exists x, N x /\ P x.
Definition d_no    (N P : Entity -> Prop) : Prop := ~ exists x, N x /\ P x.

Variables (man woman unicorn : Entity -> Prop).
Variables (walk : Entity -> Prop) (love : Entity -> Entity -> Prop).
Variable  john : Entity.

Definition every_man_walks : Prop := d_every man walk.
Definition a_man_walks     : Prop := d_a man walk.
Definition john_walks      : Prop := star john walk.

(* PTQ-T1.  T4 subject-predicate through the raised subject is the
   first-order sentence (definitional — the fragment computes). *)
Theorem john_walks_eq : john_walks = walk john.
Proof. reflexivity. Qed.

Theorem every_man_walks_eq :
  every_man_walks = forall x, man x -> walk x.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(*  Part 3 — Quantifying-in (M73 T14)                                         *)
(* ========================================================================== *)

(* The two derivations of "every man loves a woman": direct (surface,
   forall-exists) and via quantifying the object in over a pronoun
   (inverse, exists-forall). *)
Definition emlaw_surface : Prop :=
  d_every man (fun x => d_a woman (fun y => love x y)).
Definition emlaw_inverse : Prop :=
  d_a woman (fun y => d_every man (fun x => love x y)).

(* PTQ-T2.  The inverse scope entails the surface scope (the classic
   exists-forall => forall-exists); the converse is NOT provable — PTQ's
   two analysis trees are genuinely two readings. *)
Theorem inverse_entails_surface : emlaw_inverse -> emlaw_surface.
Proof.
  intros [y [Hw Hall]] x Hm; exists y; split; [exact Hw | exact (Hall x Hm)].
Qed.

(* PTQ-T3.  ... and the readings are genuinely distinct: a concrete
   model (two men, two women, crosswise love) satisfies the surface
   reading and refutes the inverse one.  Stated as an existence theorem
   over bool to stay axiom-free. *)
Theorem readings_distinct :
  exists (love2 : bool -> bool -> Prop),
    (forall x : bool, exists y : bool, love2 x y) /\
    ~ (exists y : bool, forall x : bool, love2 x y).
Proof.
  exists (fun x y => x = y).
  split.
  - intros x; exists x; reflexivity.
  - intros [y Hall].
    assert (Ht := Hall true); assert (Hf := Hall false).
    rewrite <- Ht in Hf; discriminate Hf.
Qed.

(* ========================================================================== *)
(*  Part 4 — Intensionality: seek vs find (M73; the meaning postulates)       *)
(* ========================================================================== *)

(* An intensional transitive verb takes the QUANTIFIER as its object —
   PTQ's <s,<<s,<e,t>>,t>> object, extensionalized to the GQ
   (ARTIFACT-ii). *)
Definition ITV : Type := Entity -> GQ Entity -> Prop.

(* De dicto: the quantifier is the direct argument.  De re: the
   quantifier scopes over a first-order relation to the raised object —
   PTQ's quantifying-in of the object. *)
Definition dedicto (V : ITV) (subj : Entity) (obj : GQ Entity) : Prop :=
  V subj obj.
Definition dere (V : ITV) (subj : Entity) (N : Entity -> Prop) : Prop :=
  d_a N (fun y => V subj (star y)).

(* Extensional verbs are LIFTS of first-order relations — the shape of
   PTQ's meaning postulate for find/eat/etc. *)
Definition lift (R : Entity -> Entity -> Prop) : ITV :=
  fun subj obj => obj (fun y => R subj y).

(* PTQ-T4.  For a lifted (extensional) verb, de dicto = de re: "John
   finds a unicorn" has exactly the relational reading with existential
   commitment.  This is the content of the meaning postulate. *)
Theorem find_dedicto_dere : forall (find0 : Entity -> Entity -> Prop),
  dedicto (lift find0) john (d_a unicorn) <->
  exists u, unicorn u /\ find0 john u.
Proof. intros find0; unfold dedicto, lift, d_a; tauto. Qed.

(* PTQ-T5.  De re always carries existential commitment, for ANY verb. *)
Theorem dere_existence : forall (V : ITV),
  dere V john unicorn -> exists u, unicorn u.
Proof. intros V [u [Hu _]]; exists u; exact Hu. Qed.

End PTQ.

(* PTQ-T6.  THE PTQ headline, as an axiom-free existence theorem: there
   is a model and a seek-relation where "John seeks a unicorn" (de
   dicto) is TRUE and there are NO unicorns — intensional verbs carry no
   existential commitment (M73's motivating datum). *)
Theorem seek_no_existence :
  exists (Entity : Type) (unicorn : Entity -> Prop)
         (seek : ITV Entity) (john : Entity),
    dedicto Entity seek john (d_a Entity unicorn) /\
    ~ exists u, unicorn u.
Proof.
  exists unit, (fun _ => False).
  exists (fun _ _ => True), tt.
  split; [exact I | intros [u Hu]; exact Hu].
Qed.

(* PTQ-T7.  ... while the same de dicto sentence with a LIFTED verb
   forces existence — so seek provably cannot be a lift (corollary shape
   of the seek/find contrast). *)
Theorem seek_not_liftable :
  forall (Entity : Type) (unicorn : Entity -> Prop)
         (seek0 : Entity -> Entity -> Prop) (john : Entity),
    dedicto Entity (lift Entity seek0) john (d_a Entity unicorn) ->
    exists u, unicorn u.
Proof. intros En unicorn seek0 john [u [Hu _]]; exists u; exact Hu. Qed.

(* ========================================================================== *)
(*  Part 5 — Barwise & Cooper hooks: the PTQ determiners are GQ-well-behaved  *)
(* ========================================================================== *)

Section BCHooks.

Variable Entity : Type.

(* Conservativity: D(A)(B) <-> D(A)(A cap B) — B&C 1981's universal,
   checked for the PTQ determiners (edge evidence). *)
Theorem every_conservative : forall N P : Entity -> Prop,
  d_every Entity N P <-> d_every Entity N (fun x => N x /\ P x).
Proof.
  intros N P; unfold d_every; split; intros H x Hn.
  - split; [exact Hn | exact (H x Hn)].
  - exact (proj2 (H x Hn)).
Qed.

Theorem a_conservative : forall N P : Entity -> Prop,
  d_a Entity N P <-> d_a Entity N (fun x => N x /\ P x).
Proof. intros N P; unfold d_a; split; intros [x H]; exists x; tauto. Qed.

Theorem no_conservative : forall N P : Entity -> Prop,
  d_no Entity N P <-> d_no Entity N (fun x => N x /\ P x).
Proof.
  intros N P; unfold d_no; split; intros H [x Hx]; apply H; exists x; tauto.
Qed.

(* Right monotonicity: every and a are upward, no is downward. *)
Theorem every_mon_up : forall N P Q : Entity -> Prop,
  (forall x, P x -> Q x) -> d_every Entity N P -> d_every Entity N Q.
Proof. intros N P Q Hpq H x Hn; exact (Hpq x (H x Hn)). Qed.

Theorem a_mon_up : forall N P Q : Entity -> Prop,
  (forall x, P x -> Q x) -> d_a Entity N P -> d_a Entity N Q.
Proof. intros N P Q Hpq [x [Hn Hp]]; exists x; split; [exact Hn | exact (Hpq x Hp)]. Qed.

Theorem no_mon_down : forall N P Q : Entity -> Prop,
  (forall x, Q x -> P x) -> d_no Entity N P -> d_no Entity N Q.
Proof. intros N P Q Hqp H [x [Hn Hq]]; apply H; exists x; split; [exact Hn | exact (Hqp x Hq)]. Qed.

(* Left (restrictor) monotonicity: every is downward, a is upward. *)
Theorem every_restr_down : forall N M P : Entity -> Prop,
  (forall x, M x -> N x) -> d_every Entity N P -> d_every Entity M P.
Proof. intros N M P Hmn H x Hm; exact (H x (Hmn x Hm)). Qed.

Theorem a_restr_up : forall N M P : Entity -> Prop,
  (forall x, N x -> M x) -> d_a Entity N P -> d_a Entity M P.
Proof. intros N M P Hnm [x [Hn Hp]]; exists x; split; [exact (Hnm x Hn) | exact Hp]. Qed.

End BCHooks.

(* ========================================================================== *)
(*  Part 6 — The modal layer, minimal (hook for the Kratzer edge)             *)
(* ========================================================================== *)

Section Modal.

Variable Index : Type.

(* PTQ's box, S5-flavoured: truth at every point of reference.  This is
   exactly what shallow/kratzer2.v's kratzer_equals_montague /
   empty_base_characterization compare against (edges/ptq__kratzer). *)
Definition box (p : Index -> Prop) : Index -> Prop := fun _ => forall j, p j.

Theorem box_K : forall (p q : Index -> Prop) (i : Index),
  box (fun j => p j -> q j) i -> box p i -> box q i.
Proof. intros p q i Hpq Hp j; exact (Hpq j (Hp j)). Qed.

Theorem box_Nec : forall (p : Index -> Prop),
  (forall i, p i) -> forall i, box p i.
Proof. intros p H i j; exact (H j). Qed.

Theorem box_T : forall (p : Index -> Prop) (i : Index),
  box p i -> p i.
Proof. intros p i H; exact (H i). Qed.

End Modal.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)
(* Output under Coq 8.20.1 (2026-09-05): every theorem below prints
   "Closed under the global context" (ARTIFACT-iv). *)
Print Assumptions john_walks_eq.
Print Assumptions every_man_walks_eq.
Print Assumptions inverse_entails_surface.
Print Assumptions readings_distinct.
Print Assumptions find_dedicto_dere.
Print Assumptions dere_existence.
Print Assumptions seek_no_existence.
Print Assumptions seek_not_liftable.
Print Assumptions every_conservative.
Print Assumptions a_conservative.
Print Assumptions no_conservative.
Print Assumptions every_mon_up.
Print Assumptions no_mon_down.
Print Assumptions every_restr_down.
Print Assumptions box_K.
Print Assumptions box_T.
