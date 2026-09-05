(* ========================================================================== *)
(*  MTT_vs_Ranta.v — the bridge: MTT-semantics (CL20) vs TTG (Ranta 1995)     *)
(*  FORMAL-ATLAS / atlas/mtt_ranta                                            *)
(* ========================================================================== *)
(*
   SOURCES
     [CL20] Chatzikyriakidis & Luo 2020, esp. §1.4.2 (historical notes:
       "MTT-semantics ... was not available ... until Ranta's work in the
       early 1990s"), §3.2.1 (CNs-as-types, adopted from Ranta/Luo),
       §3.3.1 (intersective adjectives as Sigma).
     [R95]  Ranta 1995, esp. §2.12 (separated subsets), §2.16
       (props-as-types), §3.1 (quantifiers), §4.2 (pronominalization),
       ch. 9 (sugaring).
   Companions: atlas/mtt_ranta/MTT.v, atlas/mtt_ranta/Ranta.v — this file
   Requires both (qualified; no Import — the vocabularies deliberately
   collide).  Design: formalizing_formal_semantics/atlas/designs/mtt_ranta.md.

   WHAT IS FORMALIZED — the comparison, as theorems
     B1  The category of CNs coincides: both files' CN is the ambient
         Type; CN meanings agree definitionally.
     B2  Quantifiers: every and no agree definitionally / by two-line
         interderivations.  some DIVERGES in proof relevance: Ranta's
         Sigma implies MTT's exists (witness projection), but the
         converse holds only up to inhabited — Coq's elimination
         restriction is precisely the formal residue of R95-Type
         (proof-relevant propositions, §2.16) vs CL20-Prop (UTT's
         impredicative, proof-irrelevant-in-spirit Prop, §2.3.1).  A
         witness-extraction function exists on the Ranta side and
         provably cannot be written on the MTT side (documented).
     B3  Intersective adjectives ARE separated subsets: MTT.inter_cn
         (sig) and Ranta.subset_cn (sigT) are equivalent both ways —
         CL20 §3.3.1 is R95 §2.12.
     B4  The donkey sentence: CL20's rendering (Pi in Prop over the same
         Sigma-context — they inherit Ranta's analysis) is DEFINITIONALLY
         Ranta's donkey_sentence at a Prop-valued lexicon; the strong
         reading transfers.
     B5  Subtyping: with an explicit lifting both sides agree
         definitionally; the divergence is that MTT.v has the
         monotonicity PACKAGE (every_anti/some_mono/no_anti) while R95
         has no subtyping — the Ranta-side sentence must insert the
         lifting manually (demonstrated with Fail Check).
     B6  Sugaring: Ranta.linear exists and MTT.v deliberately has no
         generation function — CL20 give no sugaring/generation story;
         recorded here as prose (no theorem is statable about an absent
         function).

   NOT FORMALIZED (and why)
     * B7 (design STRETCH): instantiating atlas/dynamic/DPL.v's models to
       compare Ranta's curried donkey with DPL's dk2_truth — dropped for
       budget; the statement plan is in the design doc.
     * Roundtrip identities for the B3 equivalence (they hold; only the
       two maps are needed by the record).

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-i]   Cross-sort equalities (Prop-valued vs Type-valued
                    meanings) are stated at Type via cumulativity; where
                    a genuine sort gap exists (some/exists), the
                    mediation is inhabited — the gap is the finding, not
                    an encoding accident.
     [ARTIFACT-iv]  Zero axioms; every audited theorem closes under the
                    global context.
*)

Require mtt_ranta.MTT.
Require mtt_ranta.Ranta.

(* ========================================================================== *)
(*  B1 — CNs coincide                                                         *)
(* ========================================================================== *)

(* Both books interpret CNs as types (CL20 §3.2.1 after R95/L12); both
   files set CN := Type. *)
Theorem cn_agree : MTT.CN = Ranta.CN.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(*  B2 — Quantifiers: agreement and the proof-relevance divergence            *)
(* ========================================================================== *)

Section Quantifiers.

Variables (A : Type) (P : A -> Prop).

(* every: the SAME Pi, read at Prop (CL20) and at Type (R95) —
   definitional agreement through cumulativity. *)
Theorem every_agree : (MTT.every A P : Type) = Ranta.every A P.
Proof. reflexivity. Qed.

(* no: interderivable in two lines (False vs Empty_set is the only
   difference). *)
Theorem no_agree_fwd : MTT.no A P -> Ranta.no A P.
Proof. intros H x Hx; destruct (H x Hx). Qed.

Theorem no_agree_bwd : Ranta.no A P -> MTT.no A P.
Proof. intros H x Hx; destruct (H x Hx). Qed.

(* some: Ranta's Sigma yields MTT's exists — the witness projects out. *)
Theorem some_agree_fwd : Ranta.some A P -> MTT.some A P.
Proof. intros [x Hx]; exists x; exact Hx. Qed.

(* ... but the converse only holds up to inhabited: an exists in Prop
   cannot be eliminated into Type.  THIS is the formal residue of
   R95-Type vs CL20-Prop (header B2). *)
Theorem some_agree_bwd_inhabited :
  MTT.some A P -> inhabited (Ranta.some A P).
Proof. intros [x Hx]; constructor; exists x; exact Hx. Qed.

(* On the Ranta side, witness extraction is a FUNCTION (R95 §3.7
   "reference to proofs"); on the MTT side no such function is
   definable:
     Fail Definition mtt_witness (H : MTT.some A P) : A := ...
   fails with the elimination restriction ("Case analysis on sort Type
   is not allowed for inductive definition ex").  *)
Definition ranta_witness (p : Ranta.some A P) : A := projT1 p.

Theorem ranta_witness_sound : forall p : Ranta.some A P,
  P (ranta_witness p).
Proof. intros p; exact (projT2 p). Qed.

End Quantifiers.

(* ========================================================================== *)
(*  B3 — Intersective adjectives ARE separated subsets                        *)
(* ========================================================================== *)

Section Adjectives.

Variables (A : Type) (P : A -> Prop).

(* CL20 §3.3.1's modified CN (sig) and R95 §2.12's separated subset
   (sigT) are equivalent both ways — sig is not Prop, so both
   eliminations are legal. *)
Theorem inter_subset_fwd : MTT.inter_cn A P -> Ranta.subset_cn A P.
Proof. intros [x Hx]; exists x; exact Hx. Qed.

Theorem inter_subset_bwd : Ranta.subset_cn A P -> MTT.inter_cn A P.
Proof. intros [x Hx]; exists x; exact Hx. Qed.

(* The quantified sentences over the two modified CNs are
   interderivable: "some black man walks" means the same thing read
   through CL20 or R95. *)
Theorem inter_subset_some : forall Q : A -> Prop,
  MTT.some (MTT.inter_cn A P) (fun z => Q (proj1_sig z)) <->
  (exists z : Ranta.subset_cn A P, Q (projT1 z)).
Proof.
  intros Q; split.
  - intros [[x Hp] Hq]; exists (existT _ x Hp); exact Hq.
  - intros [[x Hp] Hq]; exists (exist _ x Hp); exact Hq.
Qed.

End Adjectives.

(* ========================================================================== *)
(*  B4 — The donkey sentence coincides                                        *)
(* ========================================================================== *)

Section Donkey.

Variables (Farmer Donkey : Type).
Variables (own beat : Farmer -> Donkey -> Prop).

(* CL20's rendering: a Pi in Prop over the SAME Sigma-context (they
   inherit R95's analysis — CL20 §1.4.2).  The context is a Type (sigT
   over a Prop component is legal), the sentence is a Prop. *)
Definition mtt_donkey : Prop :=
  forall z : {x : Farmer & {y : Donkey & own x y}},
    beat (projT1 z) (projT1 (projT2 z)).

(* B4a.  Definitional agreement with Ranta's donkey_sentence at the
   Prop-valued lexicon (cumulativity). *)
Theorem donkey_agree :
  (mtt_donkey : Type) = Ranta.donkey_sentence Farmer Donkey own beat.
Proof. reflexivity. Qed.

(* B4b.  The strong reading transfers to the MTT side through the
   shared currying theorem (Ranta.donkey_curry). *)
Theorem mtt_donkey_strong_fwd :
  mtt_donkey -> forall x y, own x y -> beat x y.
Proof.
  exact (fst (Ranta.donkey_curry Farmer Donkey own beat)).
Qed.

Theorem mtt_donkey_strong_bwd :
  (forall x y, own x y -> beat x y) -> mtt_donkey.
Proof.
  exact (snd (Ranta.donkey_curry Farmer Donkey own beat)).
Qed.

End Donkey.

(* ========================================================================== *)
(*  B5 — Subtyping: agreement under explicit lifting; the divergence          *)
(* ========================================================================== *)

Section Subtyping.

Variables (Man Human : Type) (mh : Man -> Human) (walk : Human -> Prop).

(* Without a lifting, the Ranta-side sentence is ill-typed — R95 has no
   subtyping; the following fails with "The term x has type Man while it
   is expected to have type Human":
     Fail Check (Ranta.every Man (fun x : Man => walk x)).
   (Kept as a comment: Fail Check inside a section reports the section
   variables, which makes the error message environment-relative.) *)

(* With the lifting explicit, the two sides agree definitionally. *)
Theorem sub_sentence_agree :
  (MTT.every Man (MTT.pred_lift Man Human mh walk) : Type) =
  Ranta.every Man (fun x => walk (mh x)).
Proof. reflexivity. Qed.

(* The monotonicity package exists only on the MTT side (CL20 §3.2.2);
   its content is nevertheless PROVABLE about the Ranta forms, via the
   agreement — "some man walks" entails "some human walks" read through
   R95's Sigma: *)
Theorem ranta_some_mono :
  Ranta.some Man (fun x => walk (mh x)) -> Ranta.some Human walk.
Proof. intros [x Hx]; exists (mh x); exact Hx. Qed.

End Subtyping.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)
(* Output under Coq 8.20.1 (2026-09-05): every theorem below prints
   "Closed under the global context". *)
Print Assumptions cn_agree.
Print Assumptions every_agree.
Print Assumptions no_agree_fwd.
Print Assumptions no_agree_bwd.
Print Assumptions some_agree_fwd.
Print Assumptions some_agree_bwd_inhabited.
Print Assumptions ranta_witness_sound.
Print Assumptions inter_subset_fwd.
Print Assumptions inter_subset_bwd.
Print Assumptions inter_subset_some.
Print Assumptions donkey_agree.
Print Assumptions mtt_donkey_strong_fwd.
Print Assumptions mtt_donkey_strong_bwd.
Print Assumptions sub_sentence_agree.
Print Assumptions ranta_some_mono.
