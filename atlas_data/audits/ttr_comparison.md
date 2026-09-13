# Source audit: TTR, MTT, Ranta and DTS (2026-09-12)

This is an implementation/source audit, not a design plan for every author
mentioned below. It is kept outside the directory used to infer design coverage.

This supersedes the old TTR checkpoint and the claim that the four frameworks
should be compared by a general equivalence. The implemented comparisons are
restricted translations with their required assumptions and losses exposed.

## Sources actually read for this revision

- Cooper 2023, *From Perception to Communication*: section 1.3 pp. 11-14;
  section 1.4.1 pp. 18-19; A2-A3 pp. 400-401; A8-A9 pp. 404-406;
  A11.1-A11.3 pp. 407-411. These define type identity, extensions,
  ptype witness assignments, model families, records, dependency and merge.
- Chatzikyriakidis & Luo 2020: sections 1.2 and 1.4.2-1.4.3, especially
  pp. 5, 15-20; section 2.3.1 pp. 33-34; section 3.2.3 pp. 60-64.
- Ranta, *Type-Theoretical Grammar* (local filename dated 1995; cited as
  1994 by CL20/BM17): sections 2.11-2.12 pp. 33-36 and 2.16 pp. 39-40.
  The existing donkey/progressive-conjunction implementation was inspected;
  this revision is not a new source audit of the entire Ranta book.
- Bekki & Mineshima 2017, *Context-Passing and Underspecification in
  Dependent Type Semantics*: sections 1.1-1.4 pp. 11-19, section 2's
  inference tests, and sections 3.1-3.3 pp. 23-27. The on-disk filename is
  misleadingly `Bekki_Mineshima_2017_CalculatingProjectionsViaTypeChecking.pdf`.
  Bekki 2014 is still unavailable; no claim to have read it is made.

The source corpus is in the sibling `formalizing_formal_semantics/papers`
directory. Set `ATLAS_PAPERS` to that directory when rebuilding this checkout.

## The architectural distinction

Cooper section 1.3 adopts a set-theoretic account: a type is an object distinct
from its set of witnesses. Section 1.4.1 and A3.2 assign particular witnesses
through F. Two type objects can have the same extension; an assignment can
change while the type code remains fixed. Coq is the metalanguage of this
deep embedding, not the object-language TTR type system.

CL20 p. 20 explicitly call MTT semantics both model-theoretic and
proof-theoretic. They explain that the MTT itself is the meaning-carrying
language, occupying the foundational role that set theory plays in Montague
semantics. This is not the claim that MTT has Cooper's separate A/F assignment
to reified type codes. Cooper p. 14 also disputes describing his types as
merely sets or names of sets. The implementation preserves both distinctions.

## What changed in TTR

`TTR.of_ty` now tests `holds predicate arguments candidate_witness`.
Previously it ignored the candidate, so every object witnessed any true
ptype. This was not just proof irrelevance. It changed the semantics of
meet: separate existence of P and Q witnesses does not guarantee a common
witness of their meet (A8). `TTR_Model` proves that counterexample, plus
model variation with identical erased truth values, distinct coextensional
types, and failure of unconditional relabelling for structured witnesses.

The subtyping and merge proofs survive with the repaired semantics.
Relabelling in a fixed model requires a stated compatibility condition on F.
All these are assumptions of universally quantified theorems, not axioms.

`TTR_vs_MTT` fixes a model, induces a CN type from a basic extension, and
erases ptype witnesses into existential propositions. It proves agreement of
inhabitation on the man-runs construction. The return direction supplies a
propositional existence claim, not a choice function. A counterexample proves
that the subject projection loses witness information and has no inverse.
The old `TTR.Examples` hook remains a concrete example, not a framework edge.

Scope: atomic predicate arguments; basic types classify atoms; ptype witnesses
can be atoms or records; monomorphic basic arities are checked by an explicit
admissibility condition. The raw association-list carrier includes ill-formed
lists: source record claims are restricted to functional labels. General
dependent type functions, ERec, A10 stratification, and A9's varying Type_M
domains remain outside the implemented fragment. No complete semantic
subtyping algorithm or complete implementation of Cooper's mu is claimed.

## MTT and Ranta

Both support strong Sigma packages. CL20 p. 16 note 26 explicitly uses Sigma
and weak existential quantification together. `MTT.strong_some` and the new
bridge theorems make this visible. The existing weak-exists versus Sigma
comparison concerns chosen constructors; Coq's rejection of a direct
Prop-to-Type eliminator is not an impossibility theorem about MTT semantics.
Likewise an unlifted expression fails in both Coq encodings; the distinction
is coercive-subtyping machinery, not an inability to insert a function.

The Prop/Type distinction remains relevant for proof relevance and counting.
No general proof-irrelevance principle or counting theorem was added here.
Ranta's separated subsets are represented by Sigma in this encoding; source
judgemental subset membership is not literally a Coq `sigT` constructor.

## DTS and the noun ontology

BM17 section 1.4 explicitly distinguishes its `entity -> type` CN predicates
from Ranta/MTT noun types. `DTS.PredicateDTS` now implements the predicate
context, including noun evidence. Two explicit inverse context maps connect
it to Ranta after replacing each CN predicate with its Sigma witness type.
The canonical readings agree through that re-encoding, not by an assertion
that the original noun ontologies coincide. Dynamic conjunction passes both
the prior context and the new witness, as BM17 Definition 4 requires.

`MTT_vs_DTS` makes the induced noun translation explicit for a Prop-valued
fragment. It also compares quantifiers through the image of a type's lifting
into a common domain, and verifies negative predication without assuming
positive noun membership. This uses the existing simplified `MTT.in_prop`,
not the full heterogeneous IS construction of CL20 section 7.1. BM17 p. 19
acknowledges the C&L answer to the predication problem; it should not be
presented as an established impossibility of MTT.

The original shallow resolution space is now complemented by the bounded
typed calculus in `DTS_Resolution.v` (2026-09-13). See the subsequent
`revision_2026_09_13.md` audit for search guarantees and limits. The old
sorted helpers remain specializations, not an architectural equivalence.

## Rebuild

From the repository root:

```sh
coq_makefile -f _CoqProject -o Makefile
make -j4
python3 atlas_data/verify.py --all
python3 atlas_data/verify.py --lock
python3 tool/llm/signatures.py
ATLAS_PAPERS=/Users/graogro/Dropbox/formalizing_formal_semantics/papers python3 atlas_data/consolidate.py
python3 atlas_data/build_site.py
```

The 230-paper formality annotations remain frozen. New theory records do not
silently add ungraded papers or attribute Cooper 2023 results to Cooper 2005.
Mechanical checking is separate from this source audit; no second independent
semantic reviewer is claimed.

Rebuilding exposed a reporting bug: substring matching treated author names
inside ordinary words as design evidence (for example, Das in "lambdas").
Design detection now requires a complete surname token. Three previously
published false design badges (Degen, Deal, Eco; IDs 90, 98, 206) consequently
return from F2 to F1. This does not change their frozen intrinsic-formality
grades. The earlier provisional major-restructuring outcomes for DTS
(IDs 35, 38) were WITHDRAWN on 2026-09-13: an unfinished implementation
does not establish a required change to the theory. Both now withhold the
theory determination; the bounded new module does not yet justify a final
whole-source outcome either.
