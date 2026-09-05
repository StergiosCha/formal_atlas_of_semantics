(* ========================================================================== *)
(*  MTT.v — Formal semantics in modern type theories (MTT-semantics)          *)
(*  FORMAL-ATLAS / atlas/mtt_ranta                                            *)
(* ========================================================================== *)
(*
   SOURCES
     [CL20] Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in
       Modern Type Theories. ISTE/Wiley.  [ch. 2 (MTTs: Pi/Sigma, universes,
       subtyping §2.4); ch. 3 (basic categories §3.1, CNs-as-types §3.2.1,
       subtyping in semantics §3.2.2, judgmental interpretations §3.2.3,
       adjectives §3.3); ch. 4 (adverbs §4.5); ch. 5 (copredication and
       dot-types §5.2, individuation §5.3); ch. 6 (Coq); ch. 7 (§7.1
       propositional forms); App. 6 (dot-type rules); App. 7 (Coq code —
       cross-checked, not copied: it uses global Axioms/Parameters, which
       this file bans)]
     [L12]  Luo, Z. (2012). Common nouns as types. LACL 2012.  [the
       CNs-as-types thesis adopted in §3.2.1]
     [CL14] Chatzikyriakidis, S. & Luo, Z. (2014). Natural language
       inference in Coq. J. of Logic, Language and Information.  [the NLI
       suite of Part 8]
   Design document: formalizing_formal_semantics/atlas/designs/mtt_ranta.md
     (one design for the pair MTT.v / Ranta.v / MTT_vs_Ranta.v; the shared
     lexicon names of its §2 table are used verbatim so the bridge file can
     state agreement theorems).

   WHAT IS FORMALIZED
     Part 1  CNs as types: the universe CN, verbs and adjectives as
             predicates, the polymorphic quantifiers every/some/no/a
             (CL20 §3.1-3.2.1).
     Part 2  Subtyping: coercions as explicit lifting functions;
             monotonicity of some/no and anti-monotonicity of every along
             a coercion; composition; contravariant lifting on predicate
             spaces (CL20 §2.4, §3.2.2).
     Part 3  Judgmental interpretations and their propositional forms:
             in_prop c b = "b is (the image of) an A"; judgments entail
             their propositional forms; forms compose (CL20 §3.2.3, §7.1).
     Part 4  Adjectival modification, the §3.3 case study, one block per
             class: intersective (Sigma/subset CNs, the modification iff),
             subsective (polymorphic predicates; non-transferability
             across coercions PROVED by countermodel), privative (sum
             types; a fake gun is a gun-in-the-extended-sense and provably
             not a real gun), non-committal (opacity witnessed by a
             countermodel; no veridicality theorem exists).
     Part 5  Adverbs: veridical manner adverbs as Sigma-packaged predicate
             modifiers; walk_quickly |= walk (CL20 §4.5.1-4.5.2).
     Part 6  Copredication with dot-types: PhyInfo as a two-projection
             record; "John picked up and mastered the book" typechecks and
             entails both conjuncts, also under quantification
             (CL20 §5.2, App. 6).
     Part 7  Individuation (CL20 §5.3, lite): counting relative to an
             identity criterion; a concrete two-copies/one-content lexicon
             where phy-individuation counts two books and
             info-individuation refutes two.
     Part 8  An NLI mini-suite in the style of CL14/CL20 ch. 6: quantifier
             monotonicity, adjective drops, conjunction/disjunction and
             coercion inferences, as theorems over the abstract lexicon.

   NOT FORMALIZED (and why)
     * Gradable/multidimensional adjectives and gradable nouns (CL20
       §4.2-4.4): need degree structures; STRETCH in the design, dropped
       for budget.
     * Generic semantics of numerical quantifiers (§5.3.2) beyond the
       count-2 predicates of Part 7: STRETCH.
     * Dependent event types (§7.2) and dependent categorial grammars
       (§7.3 — overlaps atlas/type_logical/Lambek.v): out of scope.
     * Intensional adverbs (§4.5.4), vagueness (§4.6): out of scope.
     * TTR comparison: separate queue item.

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-i]   CL20's universe CN is a Tarski-style internal universe
                    of a Type appearing in UTT; here CN := Type
                    (Russell-style, the ambient universe).  Consequence:
                    "polymorphic over CN" means a Coq forall over Type,
                    and there is no internal induction over CN.
     [ARTIFACT-ii]  Judgments (a : A) are not reifiable inside Coq, so the
                    judgment/proposition distinction of CL20 §3.2.3 is
                    rendered one-sidedly: propositional forms (in_prop)
                    are defined and their properties proved; that a
                    judgment "holds" is represented by exhibiting a term.
     [ARTIFACT-iii] Coercive subtyping <=c is rendered by EXPLICIT lifting
                    functions (variables c : A -> B); Coq's Coercion
                    mechanism is only local sugar (a Coercion on a section
                    variable dies with the section) and Coq checks no
                    coherence.  Dot-types are encoded as two-projection
                    records — the record also has pairing, which Luo's
                    dot-types forbid; the encoding is FAITHFUL for the
                    elimination behaviour used here (App. 6).
     [ARTIFACT-iv]  Zero axioms, zero global Parameters (unlike the
                    ttr_mtt/ pilots and CL20's own App. 7): every schema
                    is forall-closed over Section variables; every demo is
                    a concrete Inductive/Definition instance.  All audited
                    theorems close under the global context.
*)

Definition CN := Type.

(* ========================================================================== *)
(*  Part 1 — CNs as types and the polymorphic quantifiers                     *)
(* ========================================================================== *)

(* CL20 §3.1 Table (basic categories): CN |-> Type in CN, IV |-> A -> Prop,
   ADJ |-> A -> Prop, S |-> Prop; §3.2.1 (CNs as types, after L12). *)
Definition every (A : CN) (P : A -> Prop) : Prop := forall x : A, P x.
Definition some  (A : CN) (P : A -> Prop) : Prop := exists x : A, P x.
Definition no    (A : CN) (P : A -> Prop) : Prop := forall x : A, ~ P x.
Definition a_indef := some.   (* the indefinite article, CL20 §3.1 *)

(* ========================================================================== *)
(*  Part 2 — Subtyping as explicit coercions                                  *)
(* ========================================================================== *)

Section Subtyping.

(* CL20 §2.4, §3.2.2: A <=c B rendered by the lifting c (ARTIFACT-iii). *)
Variables (A B C : CN).
Variable c : A -> B.      (* A <=_c B *)
Variable d : B -> C.      (* B <=_d C *)

(* Composition of coercions is composition of liftings (CL20 §2.4). *)
Definition sub_comp : A -> C := fun x => d (c x).

(* Contravariant lifting on predicate spaces: if A <= B then
   (B -> Prop) <= (A -> Prop) (CL20 §2.4 on function-type subtyping). *)
Definition pred_lift (P : B -> Prop) : A -> Prop := fun x => P (c x).

(* T-SUB1.  every is anti-monotone along a coercion: "every human walks"
   entails "every man walks" (CL20 §3.2.2). *)
Theorem every_anti : forall P : B -> Prop,
  every B P -> every A (pred_lift P).
Proof. intros P H x; exact (H (c x)). Qed.

(* T-SUB2.  some is monotone: "some man walks" entails "some human
   walks" (CL20 §3.2.2). *)
Theorem some_mono : forall P : B -> Prop,
  some A (pred_lift P) -> some B P.
Proof. intros P [x Hx]; exists (c x); exact Hx. Qed.

(* T-SUB3.  no is anti-monotone: "no human walks" entails "no man
   walks". *)
Theorem no_anti : forall P : B -> Prop,
  no B P -> no A (pred_lift P).
Proof. intros P H x Hx; exact (H (c x) Hx). Qed.

(* T-SUB4.  Lifting respects composition definitionally. *)
Theorem pred_lift_comp : forall (P : C -> Prop) (x : A),
  pred_lift (fun y => P (d y)) x = P (sub_comp x).
Proof. reflexivity. Qed.

End Subtyping.

(* ========================================================================== *)
(*  Part 3 — Judgmental interpretations and propositional forms              *)
(* ========================================================================== *)

Section PropositionalForms.

(* CL20 §3.2.3, §7.1: the judgmental interpretation of "John is a man" is
   the judgment john : Man; its propositional form at a supertype B is
   "some A maps to b" (ARTIFACT-ii). *)
Variables (A B C : CN).
Variable c : A -> B.
Variable d : B -> C.

Definition in_prop (b : B) : Prop := exists a : A, c a = b.

(* T-JP1.  A judgment entails its propositional form: from a : A we get
   the proposition "c a is an A" (CL20 §3.2.3). *)
Theorem judgment_to_prop : forall a : A, in_prop (c a).
Proof. intros a; exists a; reflexivity. Qed.

(* T-JP2.  Propositional forms compose along coercions (CL20 §7.1). *)
Theorem in_prop_compose : forall b : B,
  in_prop b -> exists a : A, d (c a) = d b.
Proof. intros b [a Ha]; exists a; rewrite Ha; reflexivity. Qed.

End PropositionalForms.

(* ========================================================================== *)
(*  Part 4 — Adjectival modification (CL20 §3.3 case study)                  *)
(* ========================================================================== *)

(* Intersective adjectives: the modified CN is the subset type
   {x : A | P x} (CL20 §3.3.1). *)
Definition inter_cn (A : CN) (P : A -> Prop) : CN := {x : A | P x}.

Section Intersective.

Variables (A : CN) (P Q : A -> Prop).

(* T-ADJ1.  Noun drop: "some black man walks" entails "some man walks"
   (CL20 §3.3.1: pi1 realises the inference). *)
Theorem inter_noun_drop :
  some (inter_cn A P) (fun z => Q (proj1_sig z)) -> some A Q.
Proof. intros [[x Hx] Hq]; exists x; exact Hq. Qed.

(* T-ADJ2.  Adjective extraction: "some black man walks" entails
   "some man is black". *)
Theorem inter_adj_drop :
  some (inter_cn A P) (fun z => Q (proj1_sig z)) -> some A P.
Proof. intros [[x Hx] _]; exists x; exact Hx. Qed.

(* T-ADJ3.  The intersective iff: quantifying over the modified CN is
   quantifying over the conjunction (CL20 §3.3.1 — intersectivity is
   exactly this equivalence). *)
Theorem intersective_iff :
  some (inter_cn A P) (fun z => Q (proj1_sig z)) <->
  some A (fun x => P x /\ Q x).
Proof.
  split.
  - intros [[x Hx] Hq]; exists x; split; assumption.
  - intros [x [Hp Hq]]; exists (exist _ x Hp); exact Hq.
Qed.

(* T-ADJ4.  every over the modified CN is the guarded universal. *)
Theorem intersective_every_iff :
  every (inter_cn A P) (fun z => Q (proj1_sig z)) <->
  every A (fun x => P x -> Q x).
Proof.
  split.
  - intros H x Hp; exact (H (exist _ x Hp)).
  - intros H [x Hp]; exact (H x Hp).
Qed.

End Intersective.

(* Subsective adjectives: a polymorphic, CN-relative predicate
   (CL20 §3.3.2: "skilful" is skilful AS an A). *)
Definition subs_cn (A : CN) (Adj : forall X : CN, X -> Prop) : CN :=
  {x : A | Adj A x}.

Section Subsective.

Variables (A : CN) (Adj : forall X : CN, X -> Prop) (Q : A -> Prop).

(* T-ADJ5.  Noun drop still holds: a skilful surgeon is a surgeon. *)
Theorem subs_noun_drop :
  some (subs_cn A Adj) (fun z => Q (proj1_sig z)) -> some A Q.
Proof. intros [[x Hx] Hq]; exists x; exact Hq. Qed.

End Subsective.

(* T-ADJ6.  Subsectivity is NOT transferable along a coercion: there is a
   CN-relative predicate, a coercion and a witness that is Adj-as-A but
   not Adj-as-B — "a skilful surgeon need not be a skilful man"
   (CL20 §3.3.2).  Countermodel: Adj X x := "X has at most one element";
   unit -> bool. *)
Theorem subsective_not_transferable :
  exists (Adj : forall X : CN, X -> Prop)
         (A B : CN) (c : A -> B) (x : A),
    Adj A x /\ ~ Adj B (c x).
Proof.
  exists (fun (X : CN) (_ : X) => forall u v : X, u = v).
  exists unit, bool, (fun _ => true), tt.
  split.
  - intros [] []; reflexivity.
  - intros H; discriminate (H true false).
Qed.

(* Privative adjectives: the CL20 §3.3.3 picture — the noun is extended
   to a sum of real and fake objects, and "gun" in the wide sense is the
   sum. *)
Section Privative.

Variables (RGun FGun : CN).

Definition Gun : CN := (RGun + FGun)%type.

Definition real_gun (g : Gun) : Prop := exists r : RGun, g = inl r.
Definition fake_gun (g : Gun) : Prop := exists f : FGun, g = inr f.

(* T-ADJ7.  A fake gun is a gun (in the extended sense): typing. *)
Theorem fake_is_gun : forall f : FGun, fake_gun (inr f).
Proof. intros f; exists f; reflexivity. Qed.

(* T-ADJ8.  A fake gun is provably not a real gun (privativity):
   CL20 §3.3.3. *)
Theorem fake_not_real : forall f : FGun, ~ real_gun (inr f).
Proof. intros f [r Hr]; discriminate Hr. Qed.

(* T-ADJ9.  Every gun is really real or fake, exclusively. *)
Theorem gun_partition : forall g : Gun,
  (real_gun g \/ fake_gun g) /\ ~ (real_gun g /\ fake_gun g).
Proof.
  intros [r | f]; split.
  - left; exists r; reflexivity.
  - intros [_ [f Hf]]; discriminate Hf.
  - right; exists f; reflexivity.
  - intros [[r Hr] _]; discriminate Hr.
Qed.

End Privative.

(* T-ADJ10.  Non-committal adjectives ("alleged"): opacity is witnessed —
   there is a predicate modifier and an instance where the modified holds
   and the unmodified fails, so NO veridicality theorem is provable
   (CL20 §3.3.4; the absence of a theorem is the datum). *)
Theorem noncommittal_witness :
  exists (op : (nat -> Prop) -> nat -> Prop) (P : nat -> Prop) (x : nat),
    op P x /\ ~ P x.
Proof.
  exists (fun _ _ => True), (fun _ => False), 0.
  split; [exact I | intros []].
Qed.

(* ========================================================================== *)
(*  Part 5 — Veridical adverbs                                                *)
(* ========================================================================== *)

(* CL20 §4.5.1-4.5.2: manner adverbs are predicate modifiers packaged
   with their veridicality proof — a Sigma over the modifier space. *)
Definition VAdv (A : CN) : Type :=
  {op : (A -> Prop) -> A -> Prop | forall P x, op P x -> P x}.

Section Adverbs.

Variables (A : CN) (walk : A -> Prop) (quick : A -> Prop).

(* T-ADV1.  Veridicality: "John walks quickly" entails "John walks" —
   by the packaged proof (CL20 §4.5.1). *)
Theorem adv_veridical : forall (adv : VAdv A) (x : A),
  proj1_sig adv walk x -> walk x.
Proof. intros adv x H; exact (proj2_sig adv walk x H). Qed.

(* T-ADV2.  The space is inhabited: intersective manner reading
   "quickly" := doing it while being quick (CL20 §4.5.2). *)
Definition quickly : VAdv A.
Proof.
  exists (fun P x => P x /\ quick x).
  intros P x [Hp _]; exact Hp.
Defined.

Theorem quickly_veridical : forall x : A,
  proj1_sig quickly walk x -> walk x.
Proof. intros x H; exact (adv_veridical quickly x H). Qed.

(* T-ADV3.  Quantified veridicality: "some A walks quickly" entails
   "some A walks" (used in the NLI suite). *)
Theorem adv_some : forall adv : VAdv A,
  some A (proj1_sig adv walk) -> some A walk.
Proof.
  intros adv [x Hx]; exists x; exact (proj2_sig adv walk x Hx).
Qed.

End Adverbs.

(* ========================================================================== *)
(*  Part 6 — Copredication with dot-types                                     *)
(* ========================================================================== *)

Section Copredication.

(* CL20 §5.2, App. 6: the dot-type Phy . Info is encoded as a record with
   both projections; a Book coerces into it and each conjunct picks its
   aspect (ARTIFACT-iii: the record also has pairing, which dot-types
   forbid — only the elimination behaviour is used). *)
Variables Phy Info : CN.

Record PhyInfo : CN := mkPhyInfo {
  phy_of  : Phy;
  info_of : Info
}.

Variables (Book : CN) (bk : Book -> PhyInfo).   (* Book <=c Phy . Info *)
Variables (pickup : Phy -> Prop) (master : Info -> Prop).

(* "x picked up and mastered the book b": each verb selects its aspect
   through the dot-type projections (CL20 §5.2 "John picked up and
   mastered the book"). *)
Definition pickup_and_master (b : Book) : Prop :=
  pickup (phy_of (bk b)) /\ master (info_of (bk b)).

(* T-DOT1.  Copredication entails each conjunct. *)
Theorem copred_left : forall b, pickup_and_master b -> pickup (phy_of (bk b)).
Proof. intros b [H _]; exact H. Qed.

Theorem copred_right : forall b, pickup_and_master b -> master (info_of (bk b)).
Proof. intros b [_ H]; exact H. Qed.

(* T-DOT2.  Under quantification: "John picked up and mastered some
   book" entails "John picked up some book" and "John mastered some
   book" (CL20 §5.3.3 shape). *)
Theorem copred_some :
  some Book pickup_and_master ->
  some Book (fun b => pickup (phy_of (bk b))) /\
  some Book (fun b => master (info_of (bk b))).
Proof.
  intros [b [H1 H2]]; split; exists b; assumption.
Qed.

(* T-DOT3.  The coercion sugar works locally: with phy_of as a local
   coercion, a Phy-predicate applies to a PhyInfo directly.  (Global
   coercions on section-parameterized records into Variable targets are
   not possible — ARTIFACT-iii.) *)
Local Coercion phy_of : PhyInfo >-> Phy.
Theorem copred_coercion_demo : forall b : Book,
  pickup_and_master b -> pickup (bk b).
Proof. intros b [H _]; exact H. Qed.

End Copredication.

(* ========================================================================== *)
(*  Part 7 — Individuation (counting relative to an identity criterion)      *)
(* ========================================================================== *)

(* CL20 §5.3: CNs come with identity criteria (setoids); how many books
   there are depends on whether books are individuated physically or
   informationally. *)
Definition count_ge_2 (A : CN) (R : A -> A -> Prop) : Prop :=
  exists x y : A, ~ R x y.

Section Individuation.

(* The concrete two-copies/one-content lexicon: two physical copies
   (bool), one informational content (unit). *)
Definition Phy0  : CN := bool.
Definition Info0 : CN := unit.
Definition Book0 : CN := bool.                       (* the two copies *)
Definition bk0 (b : Book0) : PhyInfo Phy0 Info0 :=
  mkPhyInfo Phy0 Info0 b tt.

Definition phy_eq  (a b : Book0) : Prop :=
  phy_of _ _ (bk0 a) = phy_of _ _ (bk0 b).
Definition info_eq (a b : Book0) : Prop :=
  info_of _ _ (bk0 a) = info_of _ _ (bk0 b).

(* T-IND1.  Physically individuated, there are (at least) two books. *)
Theorem two_books_phy : count_ge_2 Book0 phy_eq.
Proof.
  exists true, false; unfold phy_eq; simpl; intros H; discriminate H.
Qed.

(* T-IND2.  Informationally individuated, "two books" is refutable: the
   copies collapse (CL20 §5.3.1: picked up two books vs mastered two
   books). *)
Theorem not_two_books_info : ~ count_ge_2 Book0 info_eq.
Proof.
  intros [x [y H]]; apply H; unfold info_eq; simpl.
  destruct (info_of _ _ (bk0 x)), (info_of _ _ (bk0 y)); reflexivity.
Qed.

End Individuation.

(* ========================================================================== *)
(*  Part 8 — NLI mini-suite (CL14; CL20 ch. 6)                                *)
(* ========================================================================== *)

Section NLI.

Variables (Man Human : CN) (mh : Man -> Human).
Variables (walk talk : Human -> Prop) (black : Man -> Prop).
Variable john : Man.

(* N1.  every + inhabitant => some. *)
Theorem nli_every_some :
  every Man (pred_lift Man Human mh walk) ->
  some Man (pred_lift Man Human mh walk).
Proof. intros H; exists john; exact (H john). Qed.

(* N2.  every P + some Q => some (P and Q). *)
Theorem nli_every_and_some :
  every Human walk -> some Human talk ->
  some Human (fun x => walk x /\ talk x).
Proof. intros He [x Hx]; exists x; split; [exact (He x) | exact Hx]. Qed.

(* N3.  no is the negation of some (constructively, both directions). *)
Theorem nli_no_iff : forall (A : CN) (P : A -> Prop),
  no A P <-> ~ some A P.
Proof.
  intros A P; split.
  - intros H [x Hx]; exact (H x Hx).
  - intros H x Hx; apply H; exists x; exact Hx.
Qed.

(* N4.  Coercion monotonicity instance: "some black man walks" entails
   "some human walks" — adjective drop + subtyping composed. *)
Theorem nli_black_man_walks :
  some (inter_cn Man black) (fun z => walk (mh (proj1_sig z))) ->
  some Human walk.
Proof.
  intros H.
  apply (some_mono Man Human mh).
  exact (inter_noun_drop Man black (pred_lift Man Human mh walk) H).
Qed.

(* N5.  "John walks and talks" entails "John walks" (conjunction). *)
Theorem nli_conj : walk (mh john) /\ talk (mh john) -> walk (mh john).
Proof. intros [H _]; exact H. Qed.

(* N6.  Disjunction introduction: "John walks" entails "John walks or
   talks". *)
Theorem nli_disj : walk (mh john) -> walk (mh john) \/ talk (mh john).
Proof. intros H; left; exact H. Qed.

(* N7.  every Human => the instance at a coerced individual. *)
Theorem nli_instance : every Human walk -> walk (mh john).
Proof. intros H; exact (H (mh john)). Qed.

(* N8.  no + some yields absurdity (mini consistency check). *)
Theorem nli_no_some_absurd :
  no Human walk -> some Human walk -> False.
Proof. intros Hn [x Hx]; exact (Hn x Hx). Qed.

End NLI.

(* ========================================================================== *)
(*  Part 9 — Assumption audit                                                 *)
(* ========================================================================== *)
(* Output under Coq 8.20.1 (2026-09-05): every theorem below prints
   "Closed under the global context" — zero axioms, zero Parameters
   (ARTIFACT-iv; contrast the ttr_mtt/ pilots and CL20 App. 7). *)
Print Assumptions every_anti.
Print Assumptions some_mono.
Print Assumptions judgment_to_prop.
Print Assumptions intersective_iff.
Print Assumptions intersective_every_iff.
Print Assumptions subsective_not_transferable.
Print Assumptions fake_not_real.
Print Assumptions gun_partition.
Print Assumptions noncommittal_witness.
Print Assumptions adv_veridical.
Print Assumptions copred_some.
Print Assumptions two_books_phy.
Print Assumptions not_two_books_info.
Print Assumptions nli_black_man_walks.
