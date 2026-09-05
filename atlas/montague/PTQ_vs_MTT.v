(* ========================================================================== *)
(*  PTQ_vs_MTT.v — lineage edge: Montague 1973 vs MTT-semantics (CL20)        *)
(*  FORMAL-ATLAS / atlas/montague                                             *)
(* ========================================================================== *)
(*
   The claim graded here (edges/ptq__mtt.json): the deep disagreement
   between Montague semantics and MTT-semantics is the CATEGORY OF COMMON
   NOUNS — predicates over one domain (PTQ) vs types (CL20 §3.2.1) — yet on
   quantified sentences the two are PROVABLY equivalent: quantification
   over the subset-type {x : Entity | man x} is exactly PTQ's guarded
   quantification over the single domain.  So the divergence is
   architectural (many-sorted vs single-sorted, selection restrictions as
   type errors vs category mistakes being sentences), while the truth
   conditions agree (grade 4: provable equivalence, not definitional —
   the quantification DOMAINS differ).

   What is NOT statable on each side (recorded in the edge JSON, not as
   theorems): PTQ cannot even express a selection restriction (every
   predicate applies to the whole domain); MTT.v cannot state "the domain
   of all entities" without reassembling it as a sum — CL20's CNs do not
   form one type.

   SOURCES: M73 (via atlas/montague/PTQ.v); CL20 §3.2-3.3 (via
   atlas/mtt_ranta/MTT.v); Luo 2012 (CNs as types).
*)

Require montague.PTQ.
Require mtt_ranta.MTT.

Section Edge.

Variables (Entity : Type) (man walk : Entity -> Prop).

(* The MTT rendering of the PTQ lexicon: the CN "man" becomes the subset
   TYPE carved out of PTQ's single domain (the canonical comparison move,
   used by CL20 themselves when discussing Montague, ch. 1). *)
Definition ManT : Type := MTT.inter_cn Entity man.
Definition walkT (z : ManT) : Prop := walk (proj1_sig z).

(* E1.  "every man walks": MTT-quantification over the type ManT is
   PTQ's guarded universal — both directions. *)
Theorem mtt_ptq_every :
  MTT.every ManT walkT <-> PTQ.d_every Entity man walk.
Proof.
  split.
  - intros H x Hm; exact (H (exist _ x Hm)).
  - intros H [x Hm]; exact (H x Hm).
Qed.

(* E2.  "a/some man walks": MTT-existential over ManT is PTQ's
   restricted existential. *)
Theorem mtt_ptq_some :
  MTT.some ManT walkT <-> PTQ.d_a Entity man walk.
Proof.
  split.
  - intros [[x Hm] Hw]; exists x; split; assumption.
  - intros [x [Hm Hw]]; exists (exist _ x Hm); exact Hw.
Qed.

(* E3.  "no man walks". *)
Theorem mtt_ptq_no :
  MTT.no ManT walkT <-> PTQ.d_no Entity man walk.
Proof.
  split.
  - intros H [x [Hm Hw]]; exact (H (exist _ x Hm) Hw).
  - intros H [x Hm] Hw; apply H; exists x; split; assumption.
Qed.

(* E4.  The equivalences commute with the B&C properties: conservativity
   transfers through the encoding (sample: every). *)
Theorem conservativity_transfers :
  MTT.every ManT walkT <->
  PTQ.d_every Entity man (fun x => man x /\ walk x).
Proof.
  split.
  - intros H; apply (PTQ.every_conservative Entity man walk).
    apply mtt_ptq_every; exact H.
  - intros H; apply mtt_ptq_every.
    apply (PTQ.every_conservative Entity man walk); exact H.
Qed.

End Edge.

(* E5 (prose, no theorem).  The architectural divergence — "selection
   restrictions are type errors" — is META-level and not statable inside
   Coq from either side: PTQ's walk(the-number-two) is a sentence
   (possibly false), MTT's is not a term (
     Fail Check (walkT (exist _ two two_is_a_man))
   fails already at the witness, and cross-CN application fails at
   typing).  Recorded in edges/ptq__mtt.json with grade 0 (not
   statable): the frameworks are not looking at this phenomenon with
   comparable instruments — which is exactly what the grade-0 category
   is for. *)

(* Assumption audit. *)
Print Assumptions mtt_ptq_every.
Print Assumptions mtt_ptq_some.
Print Assumptions mtt_ptq_no.
Print Assumptions conservativity_transfers.
