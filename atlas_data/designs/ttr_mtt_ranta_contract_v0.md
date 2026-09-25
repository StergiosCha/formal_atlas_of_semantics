# Comparison contract v0: witnesses, meet and model variation

Status: bounded implementation completed on 2026-09-25 in
[Witness_Contract.v](../../atlas/ttr/Witness_Contract.v): 30 checked statements,
not a whole-theory relationship or a source-level outcome. See the
[implementation/source notes](../audits/witness_contract_2026_09_25.md) for
rechecked passages, exact scope, assumptions and named results.

## First question

When does agreement of inhabitation also preserve witness identity, and what
additional structure is needed to express that preservation across TTR, MTT
and Ranta's account?

Compare a bounded fragment before proposing any whole-theory relationship.
Keep object-language TTR type codes and its external assignments distinct from
the ambient Coq types used to encode MTT and Ranta. Do not characterize MTT as
having no model-theoretic aspect: CL20 p. 20 explicitly describes both model-
and proof-theoretic aspects. The question concerns the particular assignment
architecture, not the existence of any mathematical models for type theory.

## Source anchors

Cooper pp. 11–14 and A8–A9, CL20 pp. 15–16 and 19–21, and Ranta
§2.11–2.12 and §2.16 were rechecked for this implementation. The broader
anchors below remain contextual references to the prior source audit, not
a claim that every listed passage was reread in this revision.

- Cooper 2023, sections 1.3 and 1.4.1; A3 and A8-A9: type identity, witness
  assignments, same-witness meet and model families.
- Chatzikyriakidis and Luo 2020, sections 1.4.2-1.4.3 and 2.3.1, p. 16 note 26,
  and section 3.3.1: foundational role, weak existential versus strong Sigma,
  and intersective modification.
- Ranta, sections 2.11-2.12 and 2.16: subset representation and proof relevance.
  The local file/survey says 1995 while CL20 cites 1994; edition identity remains
  unresolved and must not be silently asserted by this contract.

## Three separate observation interfaces

1. Inhabitation: does any witness exist?
2. Witness-sensitive observation: which carrier object is the witness, and can
   two distinct carrier objects be distinguished? Do not silently equate this
   with identity of Coq proof terms.
3. Model-indexed observation: with type code and candidate witness held fixed,
   how does satisfaction change when the explicit TTR assignment changes?

Agreement for interface 1 does not entail agreement for interfaces 2 or 3.

## Implemented fragment and explicit representation choice

Start with one fixed carrier W and two witness predicates P and Q. Compare:

- shared-witness packages: Sigma w:W. (P(w) x Q(w));
- independent-witness packages: (Sigma w:W. P(w)) x (Sigma w:W. Q(w)).

Here x denotes product and Sigma is witness-bearing. The generic package layer
permits Type-valued fibres and uses MTT.strong_package and Ranta.some. The TTR
instance uses Prop-valued satisfaction and MTT.strong_some. The shared carrier
and witness identity criterion are explicit
comparison infrastructure, not automatically identical native noun ontologies.

The implemented map splits a shared package into independent packages. Its
image is exactly the pairs with equal carrier projections. Joining uses an
explicit equality proof; the specified join/split equations need no added
axioms. They do not assert equality of packages containing arbitrary alignment
proofs. The TTR conversion claims carrier-level round trips, not evidence-term
round trips through the satisfaction proof.

This is a bounded contract, not a claim that the source theories interpret
their conjunction or meet by interchangeable constructors.

## Existing evidence and outstanding obligations

[TTR_Model.v](../../atlas/ttr/TTR_Model.v) already proves meet_same_witness and
Countermodels.inhabited_conjuncts_empty_meet. Its assignment countermodels show
that erased inhabitation can agree while candidate-witness typing differs.

[MTT_vs_Ranta.v](../../atlas/mtt_ranta/MTT_vs_Ranta.v) already proves agreement
of selected strong Sigma constructors and witnesses. Its weak-existential
comparison does not establish an impossibility theorem about MTT.

[TTR_vs_MTT.v](../../atlas/ttr/TTR_vs_MTT.v) proves pointwise fixed-model
inhabitation agreement and failure of an inverse for the displayed subject
projection. It does not exclude all possible richer translations.

The new module instantiates these encodings for zero-arity ptypes and binary
meet. Atom-level assignment preservation/reflection extends to this syntax;
transport and splitting commute at carrier observations. Recoverability needs
a left-inverse carrier map; target-wide inhabitation reflection additionally
uses surjectivity. Atomic truth agreement alone is refuted as a sufficient
condition by two admissible models with different meet inhabitation.

Outstanding work: source-specific noun ontologies, dependent records and
contexts, varying type domains, and an appropriate model/signature relation.
Quantifying a pointwise theorem over M is still not, by itself, a theorem about
compatibility between different models or recovery of their structure.

## Acceptance boundary

Require named Coq statements, assumption audits, counterexample scope and a
source-to-code review for every proposed relationship. Do not accept an opaque
copy of the source representation as evidence of native theoretical agreement.
No default theoretical-equivalence judgment, scalar score, P/F change or outcome
promotion follows from this draft. General record dependency, varying Type_M
domains, unrestricted subtyping, generation and DTS resolution remain outside
this first contract.
