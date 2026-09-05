(* ========================================================================== *)
(*  Ranta.v — Type-Theoretical Grammar (Ranta 1995)                           *)
(*  FORMAL-ATLAS / atlas/mtt_ranta                                            *)
(* ========================================================================== *)
(*
   SOURCES
     [R95] Ranta, A. (1995). Type-Theoretical Grammar. OUP.  (djvu in the
       folder root of formalizing_formal_semantics; text via djvutxt; djvu
       page ~ printed page + 12.  Cited by SECTION.)
       [ch. 2 (gradual introduction: §2.11 substantival and adjectival
        terms, §2.12 separated subsets, §2.16 propositions as types,
        §2.18-2.21 quantifiers/connectives); ch. 3 (logical operators in
        English: §3.1 quantifiers, §3.2 ordering principles, §3.5
        sugarings of Sigma and Pi, §3.7 reference to proofs of Pi
        propositions, §3.8 disjunction, §3.9 negation); ch. 4 (anaphora:
        §4.2 the pronominalization rule, §4.13 discourse referents);
        ch. 6 (text and discourse: §6.1 text as a progressive
        conjunction, §6.2 text as a context); ch. 9 (sugaring and
        parsing: §1.7 generation/parsing/sugaring, §9.9 conditions of
        sugarability)]
   Design document: formalizing_formal_semantics/atlas/designs/mtt_ranta.md
     (one design for the pair MTT.v / Ranta.v / MTT_vs_Ranta.v; shared
     lexicon names, so the bridge can state agreement theorems).

   WHAT IS FORMALIZED
     Part 1  The propositions-as-types logic kit at Type: every = Pi,
             some = Sigma, disjunction = sum, negation = -> Empty_set,
             conjunction = prod; separated subsets {x : A & B x} for
             substantival modification (R95 §2.11-2.21, §2.12).
     Part 2  Quantifier sentences and the ordering principle: "every man
             walks", "some man walks", "no man walks"; "every man owns a
             donkey" as Pi-over-Sigma; the type-theoretic choice
             isomorphism (Pi x. Sigma y. R) ~ (Sigma f. Pi x. R x (f x)),
             Ranta's "reference to proofs" (R95 §3.1-3.2, §3.7).
     Part 3  The donkey sentence: the context Sigma x:Farmer. Sigma
             y:Donkey. own x y; pronouns he/it as PROJECTIONS out of the
             context (the §4.2 pronominalization rule, literally); the
             sentence as Pi over the context; THE currying equivalence
             with the doubly-universal reading — the strong reading is a
             theorem, not a stipulation (R95 §3.2, §4.2).
     Part 4  Text as progressive conjunction: a two-sentence discourse as
             a telescope (nested Sigma); Sigma-associativity as the
             context-manipulation workhorse; discourse pronouns as
             projections (R95 §6.1-6.2).
     Part 5  A deep-embedded fragment with SUGARING: a small tree grammar
             (every/some/a + noun + verb; the donkey conditional), a
             type-valued semantics [denote] over an abstract lexicon, and
             a linearization [linear] to word lists; theorems that the
             example trees denote exactly the Part 2-3 meanings
             (reflexivity) and linearize to the R95 example strings
             (reflexivity); sugaring is many-to-one: "some"/"a" trees
             share a denotation and differ in string (R95 §1.7, ch. 9,
             §9.9).

   NOT FORMALIZED (and why)
     * Parsing as the inverse of sugaring (R95 §9.7) with a roundtrip
       theorem: STRETCH in the design, dropped for budget.
     * Definite phrases, the genitive, nested anaphora (§4.3-4.7):
       need Ranta's full context calculus; out of scope for the fragment.
     * Temporal reference (ch. 5), belief contexts (ch. 7), questions
       (§6.11-6.14), higher-level type theory (ch. 8), the ALF appendix:
       out of scope.
     * Morphology: linearization emits atomic words (w_walks), no
       agreement machinery (R95 ch. 10 territory).

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-i]   Propositions are Coq Types (R95 §2.16 taken
                    literally).  Equivalences are therefore pairs of
                    functions (prod), not iff; theorems with Type
                    content are Definitions/Theorems whose statements
                    live in Type.
     [ARTIFACT-ii]  Ranta's contexts are judgmental telescopes
                    (x : A, y : B x, ...); here they are REIFIED as
                    nested Sigma-types, and "what is given in context"
                    (§4.9) becomes a bound variable of the reified
                    context type.  The pronominalization rule then IS
                    projT1/projT2 composition.
     [ARTIFACT-iii] The deep fragment is a finite toy: Ranta's sugaring
                    operates schematically on open-ended type-theoretic
                    syntax; here both the tree grammar and the word list
                    are small Inductives, so sugaring adequacy is
                    checkable by reflexivity/vm_compute.
     [ARTIFACT-iv]  Zero axioms, zero global Parameters: schemata are
                    forall-closed over Section variables; demos are
                    concrete Inductives.  All audited theorems close
                    under the global context.
*)

Definition CN := Type.

(* ========================================================================== *)
(*  Part 1 — Propositions as types (R95 §2.16-2.21)                           *)
(* ========================================================================== *)

(* §2.19 universal quantification; §2.18 existential; §3.1. *)
Definition every (A : CN) (B : A -> Type) : Type := forall x : A, B x.
Definition some  (A : CN) (B : A -> Type) : Type := {x : A & B x}.
Definition a_indef := some.                          (* §3.5 *)

(* §2.20 disjunction; §2.21 absurdity and negation; §2.19 implication
   as a special case of Pi; conjunction as a special case of Sigma. *)
Definition ror  (A B : Type) : Type := (A + B)%type.
Definition rand (A B : Type) : Type := (A * B)%type.
Definition rnot (A : Type)   : Type := A -> Empty_set.
Definition rimp (A B : Type) : Type := A -> B.
Definition no (A : CN) (B : A -> Type) : Type := forall x : A, B x -> Empty_set.

(* §2.11-2.12: substantival modification is the separated subset — the
   SAME Sigma as the existential (Ranta stresses the coincidence). *)
Definition subset_cn (A : CN) (B : A -> Type) : CN := {x : A & B x}.

(* Equivalence of Type-propositions: a pair of functions (ARTIFACT-i). *)
Definition tequiv (A B : Type) : Type := (A -> B) * (B -> A).

(* ========================================================================== *)
(*  Part 2 — Quantifier sentences and ordering (R95 §3.1-3.2, §3.7)           *)
(* ========================================================================== *)

Section Quantifiers.

Variables (Man Farmer Donkey : CN).
Variables (walk talk : Man -> Type).
Variable  own : Farmer -> Donkey -> Type.

(* "every man owns a donkey" is Pi-over-Sigma, with the existential
   INSIDE — the §3.2 ordering principle read off the sugaring of §3.5. *)
Definition every_man_walks : Type := every Man walk.
Definition some_man_walks  : Type := some Man walk.
Definition no_man_walks    : Type := no Man walk.
Definition every_farmer_owns_a_donkey : Type :=
  every Farmer (fun x => some Donkey (fun y => own x y)).

(* R-Q1.  no = every-not (R95 §3.9: negation via -> Empty). *)
Theorem no_every_not :
  tequiv no_man_walks (every Man (fun x => rnot (walk x))).
Proof. split; intros H x Hx; exact (H x Hx). Qed.

(* R-Q2.  The type-theoretic choice iso: a proof of "every farmer owns a
   donkey" IS a donkey-choosing function together with ownership proofs —
   Ranta's "reference to proofs of Pi propositions" (§3.7); the modus
   ponens-like sugarings live on this. *)
Theorem ac_iso :
  tequiv every_farmer_owns_a_donkey
         {f : Farmer -> Donkey & forall x : Farmer, own x (f x)}.
Proof.
  split.
  - intros H.
    exists (fun x => projT1 (H x)).
    intros x; exact (projT2 (H x)).
  - intros [f Hf] x; exists (f x); exact (Hf x).
Qed.

(* R-Q3.  some over a separated subset flattens (the §2.12 coincidence
   at work): "some man who walks talks" = some man both walks and
   talks. *)
Theorem subset_some_flatten : forall Q : Man -> Type,
  tequiv (some (subset_cn Man walk) (fun z => Q (projT1 z)))
         (some Man (fun x => rand (walk x) (Q x))).
Proof.
  intros Q; split.
  - intros [[x Hw] Hq]; exists x; exact (Hw, Hq).
  - intros [x [Hw Hq]]; exists (existT _ x Hw); exact Hq.
Qed.

End Quantifiers.

(* ========================================================================== *)
(*  Part 3 — The donkey sentence and pronominalization (R95 §3.2, §4.2)       *)
(* ========================================================================== *)

Section Donkey.

Variables (Farmer Donkey : CN).
Variable  own  : Farmer -> Donkey -> Type.
Variable  beat : Farmer -> Donkey -> Type.

(* The antecedent "a farmer owns a donkey" as a context (discourse
   referents, §4.13): a Sigma-telescope. *)
Definition donkey_ctx : CN :=
  {x : Farmer & {y : Donkey & own x y}}.

(* The pronominalization rule (§4.2): a pronoun refers by PROJECTION out
   of the context. *)
Definition he (z : donkey_ctx) : Farmer := projT1 z.
Definition it (z : donkey_ctx) : Donkey := projT1 (projT2 z).

(* "If a farmer owns a donkey, he beats it": Pi over the context, the
   pronouns being the projections — R95's celebrated analysis (§3.2,
   §4.2). *)
Definition donkey_sentence : Type :=
  forall z : donkey_ctx, beat (he z) (it z).

(* R-D1.  THE theorem: the Sigma-analysis is equivalent to the strong,
   doubly-universal reading — currying, constructive, both directions.
   In DPL this is dk2's truth condition (atlas/dynamic/DPL.v dk2_truth);
   in R95 it is what justifies the pronominalization rule. *)
Theorem donkey_curry :
  tequiv donkey_sentence
         (forall (x : Farmer) (y : Donkey), own x y -> beat x y).
Proof.
  split.
  - intros H x y Ho; exact (H (existT _ x (existT _ y Ho))).
  - intros H [x [y Ho]]; exact (H x y Ho).
Qed.

(* R-D2.  The proof-referencing reading: given the choice-function view
   of the antecedent (R-Q2), the donkey sentence specializes to every
   farmer beating his chosen donkey. *)
Theorem donkey_choice : donkey_sentence ->
  forall (f : Farmer -> Donkey) (Hf : forall x, own x (f x)) (x : Farmer),
    beat x (f x).
Proof.
  intros H f Hf x.
  exact (fst donkey_curry H x (f x) (Hf x)).
Qed.

End Donkey.

(* ========================================================================== *)
(*  Part 4 — Text as progressive conjunction (R95 §6.1-6.2)                   *)
(* ========================================================================== *)

Section Text.

Variables (Man : CN) (walk talk : Man -> Type).

(* "A man walks. He talks." — the second sentence is interpreted IN the
   context created by the first (§6.1 "text as a progressive
   conjunction", §6.2 "text as a context"); the discourse pronoun is
   again a projection. *)
Definition text2 : Type :=
  {p : {x : Man & walk x} & talk (projT1 p)}.

(* R-T1.  Sigma-associativity — the context-manipulation workhorse: a
   progressively built text collapses to a single telescope. *)
Theorem sigma_assoc : forall (A : CN) (B C : A -> Type),
  tequiv {p : {x : A & B x} & C (projT1 p)}
         {x : A & rand (B x) (C x)}.
Proof.
  intros A B C; split.
  - intros [[x Hb] Hc]; exists x; exact (Hb, Hc).
  - intros [x [Hb Hc]]; exists (existT _ x Hb); exact Hc.
Qed.

(* R-T2.  The instance: the two-sentence discourse says a man both walks
   and talks. *)
Theorem text2_flatten :
  tequiv text2 {x : Man & rand (walk x) (talk x)}.
Proof. exact (sigma_assoc Man walk talk). Qed.

End Text.

(* ========================================================================== *)
(*  Part 5 — The fragment and sugaring (R95 §1.7, ch. 9)                      *)
(* ========================================================================== *)

(* The surface vocabulary (ARTIFACT-iii: atomic words, no morphology). *)
Inductive word : Set :=
| w_every | w_some | w_a | w_no
| w_man | w_farmer | w_donkey
| w_walks | w_talks | w_owns | w_beats
| w_if | w_comma | w_he | w_it | w_who.

(* The tree grammar: quantified sentences, a relative-clause CN, and the
   donkey conditional (the configurations R95 ch. 3-4 sugar). *)
Inductive noun : Set := n_man | n_farmer | n_donkey.
Inductive iverb : Set := v_walks | v_talks.
Inductive tverb : Set := v_owns | v_beats.

Inductive tree : Set :=
| t_every     : noun -> iverb -> tree
| t_some      : noun -> iverb -> tree
| t_a         : noun -> iverb -> tree
| t_no        : noun -> iverb -> tree
| t_every_rel : noun -> iverb -> iverb -> tree  (* every N who V1s V2s *)
| t_if_a      : noun -> tverb -> noun -> tverb -> tree.
                (* if a N1 V1s a N2, he V2s it *)

(* Linearization = sugaring to a word string (R95 §1.7: sugaring maps
   type-theoretic structure to surface strings; ch. 9). Purely
   syntactic, computable. *)
Definition lnoun (n : noun) : word :=
  match n with n_man => w_man | n_farmer => w_farmer | n_donkey => w_donkey end.
Definition liverb (v : iverb) : word :=
  match v with v_walks => w_walks | v_talks => w_talks end.
Definition ltverb (v : tverb) : word :=
  match v with v_owns => w_owns | v_beats => w_beats end.

Definition linear (t : tree) : list word :=
  match t with
  | t_every n v       => cons w_every (cons (lnoun n) (cons (liverb v) nil))
  | t_some n v        => cons w_some  (cons (lnoun n) (cons (liverb v) nil))
  | t_a n v           => cons w_a     (cons (lnoun n) (cons (liverb v) nil))
  | t_no n v          => cons w_no    (cons (lnoun n) (cons (liverb v) nil))
  | t_every_rel n v1 v2 =>
      cons w_every (cons (lnoun n) (cons w_who
        (cons (liverb v1) (cons (liverb v2) nil))))
  | t_if_a n1 tv n2 tv2 =>
      cons w_if (cons w_a (cons (lnoun n1) (cons (ltverb tv)
        (cons w_a (cons (lnoun n2) (cons w_comma
          (cons w_he (cons (ltverb tv2) (cons w_it nil)))))))))
  end.

Section FragmentSemantics.

(* The abstract lexicon (shared names with MTT.v, design §2 table). *)
Variables (Man Farmer Donkey : CN).

Definition sem_noun (n : noun) : CN :=
  match n with n_man => Man | n_farmer => Farmer | n_donkey => Donkey end.

Variable ivsem : forall n : noun, iverb -> sem_noun n -> Type.
Variable tvsem : forall n m : noun, tverb -> sem_noun n -> sem_noun m -> Type.

(* The type-valued semantics: R95's interpretations of the sugared
   configurations, clause by clause. *)
Definition denote (t : tree) : Type :=
  match t with
  | t_every n v => every (sem_noun n) (ivsem n v)
  | t_some n v  => some (sem_noun n) (ivsem n v)
  | t_a n v     => a_indef (sem_noun n) (ivsem n v)
  | t_no n v    => no (sem_noun n) (ivsem n v)
  | t_every_rel n v1 v2 =>
      every (subset_cn (sem_noun n) (ivsem n v1))
            (fun z => ivsem n v2 (projT1 z))
  | t_if_a n1 tv n2 tv2 =>
      donkey_sentence (sem_noun n1) (sem_noun n2)
                      (tvsem n1 n2 tv) (tvsem n1 n2 tv2)
  end.

(* -------------------------------------------------------------------- *)
(*  Sugaring adequacy theorems (R95 ch. 9; all by reflexivity —          *)
(*  ARTIFACT-iii makes them checkable).                                  *)
(* -------------------------------------------------------------------- *)

(* R-S1.  "every man walks" (R95 §3.1 example shape). *)
Theorem sugar_every_man_walks :
  linear (t_every n_man v_walks) =
  cons w_every (cons w_man (cons w_walks nil)).
Proof. reflexivity. Qed.

Theorem denote_every_man_walks :
  denote (t_every n_man v_walks) = every Man (ivsem n_man v_walks).
Proof. reflexivity. Qed.

(* R-S2.  The donkey conditional sugars to the R95 string and denotes
   the Part 3 analysis (§3.2, §4.2). *)
Theorem sugar_donkey :
  linear (t_if_a n_farmer v_owns n_donkey v_beats) =
  cons w_if (cons w_a (cons w_farmer (cons w_owns
    (cons w_a (cons w_donkey (cons w_comma
      (cons w_he (cons w_beats (cons w_it nil))))))))).
Proof. reflexivity. Qed.

Theorem denote_donkey :
  denote (t_if_a n_farmer v_owns n_donkey v_beats) =
  donkey_sentence Farmer Donkey
                  (tvsem n_farmer n_donkey v_owns)
                  (tvsem n_farmer n_donkey v_beats).
Proof. reflexivity. Qed.

(* R-S3.  The strong reading of the sugared donkey tree — R-D1 through
   the fragment. *)
Theorem denote_donkey_strong :
  tequiv (denote (t_if_a n_farmer v_owns n_donkey v_beats))
         (forall (x : Farmer) (y : Donkey),
            tvsem n_farmer n_donkey v_owns x y ->
            tvsem n_farmer n_donkey v_beats x y).
Proof.
  exact (donkey_curry Farmer Donkey
           (tvsem n_farmer n_donkey v_owns)
           (tvsem n_farmer n_donkey v_beats)).
Qed.

(* R-S4.  The relative clause denotes quantification over the separated
   subset (§2.12 through the fragment): "every man who walks talks". *)
Theorem denote_every_rel :
  denote (t_every_rel n_man v_walks v_talks) =
  every (subset_cn Man (ivsem n_man v_walks))
        (fun z => ivsem n_man v_talks (projT1 z)).
Proof. reflexivity. Qed.

(* R-S5.  Sugaring is many-to-one (§9.9 conditions of sugarability):
   "some man walks" and "a man walks" share their denotation and differ
   in string. *)
Theorem sugar_many_to_one :
  (denote (t_some n_man v_walks) = denote (t_a n_man v_walks)) /\
  linear (t_some n_man v_walks) <> linear (t_a n_man v_walks).
Proof.
  split.
  - reflexivity.
  - intros H; discriminate H.
Qed.

End FragmentSemantics.

(* ========================================================================== *)
(*  Part 6 — Assumption audit                                                 *)
(* ========================================================================== *)
(* Output under Coq 8.20.1 (2026-09-05): every theorem below prints
   "Closed under the global context" — zero axioms, zero Parameters
   (ARTIFACT-iv). *)
Print Assumptions no_every_not.
Print Assumptions ac_iso.
Print Assumptions subset_some_flatten.
Print Assumptions donkey_curry.
Print Assumptions donkey_choice.
Print Assumptions sigma_assoc.
Print Assumptions text2_flatten.
Print Assumptions sugar_every_man_walks.
Print Assumptions denote_every_man_walks.
Print Assumptions sugar_donkey.
Print Assumptions denote_donkey.
Print Assumptions denote_donkey_strong.
Print Assumptions denote_every_rel.
Print Assumptions sugar_many_to_one.
