# Pre-implementation inventories

These inventories follow the frozen protocol. They are source readings, not
claims that the whole selected works have been formalized.

## Grice, printed pp. 49-52 and 56-58 (P1)

Ontology: utterances, what is said, conversational context, speaker beliefs,
hearer reasoning, and conversational principles. No formal state space or
decision procedure for relevance is specified (p. 46 acknowledges difficulties).

Definitions: p. 49-50 gives three conditions on conversational implicature:
presumed cooperation; a required supposition about the speaker's belief;
recognizability of that requirement. These are not just material implication
from what is said. Pp. 57-58 give cancellation and non-entailment diagnostics.

Attempt: a relational constraint representation of the three conditions,
with explicit parameters for compatibility and recognizability. Use the
garage/petrol example p. 51: literal garage existence does not ensure an open,
petrol-selling garage; the conclusion is about belief/possibility, not fact.
Test the p. 57 cancellation diagnostic by removing the cooperation presumption.

Boundary: no derivation of relevance, belief, or mutual recognition from raw
language is supplied. The glossary fields are NOT axioms making all utterances
cooperative. The fragment cannot substantiate a whole-theory determination.

## Tarski, printed pp. 343-345, 349-353; notes 15-16 (P2)

Ontology: object-language formulas and variable assignments; their names and
satisfaction in a distinct metalanguage. Definitions: recursive satisfaction,
sentences without free variables, truth as satisfaction by all assignments.
Convention T is an adequacy SCHEMA, explicitly not itself a truth definition.

Attempt: named-variable first-order syntax with atomic predicates, conjunction,
negation and universal quantification. Prove satisfaction depends only on free
variables, hence closed-sentence assignment invariance, and the snow instance.
Boundary test: a closed contradiction has no satisfying assignment. The chosen
signature has a distinguished snow object (nonempty domain), no internal truth
predicate and no diagonal syntax. This is a language-specific construction,
not a mechanized undefinability theorem. No claim of classical bivalence in
Coq without classical assumptions; the proved fragment is constructive.

## Davidson, printed pp. 81-83 and 90-93 (P3)

PDF has no text layer; locally OCRed, with the key printed formula page checked
against the scan. Ontology: individuals and events. Definitions: action verbs
gain an event argument, with existential closure; modifiers share that event.
P. 92 (17) uses a three-place Kicked predicate, not a neo-Davidsonian thematic
role decomposition. P. 93 (18)-(20) gives modifier dropping and equality
substitution. P. 81 warns separate existential events lose shared-event content.

Attempt: generic action predicate over agent, object and event; modifier-list
conjunction and existential closure; dropping modifiers, equal-name replacement,
and a two-event countermodel to merging separately witnessed modifiers.
Motivating instance: buttering in the bathroom with a knife at midnight,
pp. 82-83. Exclude deliberately and slowly: p. 82 explicitly brackets intention
and the reference-class issue, so treating them as arbitrary intersective event
predicates would be an unwarranted extension. No full action/agency theory.
