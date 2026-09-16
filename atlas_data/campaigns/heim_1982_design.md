# Heim 1982 — full-source implementation plan and requirements ledger

2026-09-15. Authorized implementation, following the source-review draft.
Source: the 2011 Schoubye–Glick retypesetting of the 1982 dissertation in the
local corpus. All page numbers below refer to that edition. The target is the
final theory, not just the preliminary rule at p. 228 and not Heim 1983 silently
substituted for the dissertation. Existing unsuccessful attempts remain intact.

## Coverage targets, fixed before implementation

| ID | Source | Implementation / test target |
| --- | --- | --- |
| H01 | III.1.4 pp.185–190; III.2.1.1 pp.196–198 | Worlds, arbitrary individual domains, infinite assignments; independent domain and satisfaction components, world projection, distinct false files. |
| H02 | p.197 condition B | Single-coordinate invariance outside the file domain, preserved by interpretation. Distinguish it from the stronger full agreement-on-domain property; do not silently equate them. |
| H03 | III.4.4 p.234 I–IV; p.254 fn.28 V | All final rules: finite-arity atoms, sequential composition, universal restrictor with existential nuclear closure, negation with existential closure, and the proposed disjunction rule. |
| H04 | pp.202,208–211,236–238 | Local NFC and extended descriptive-content condition, including complex definite descriptions; undefinedness kept separate from falsity. |
| H05 | pp.214–218 | File truth and contextual utterance truth/falsity; existential force of fresh indefinites; discourse anaphora. |
| H06 | pp.228–234 | Correct universal donkey truth conditions; fresh nuclear-scope existential; old referents fixed; quantifier/negation/disjunction do not export tentative cards. |
| H07 | p.238 fn.21 | Nontrivial entailed descriptive content forces familiarity; expose any use of classical reasoning. |
| H08 | pp.236–237 | Presupposition entailment across all worlds, contextual filtering and local projection. |
| H09 | pp.239–241 | Accommodation as a constrained repair relation; bridges to old cards or utterance situation; do not infer an automatic bridge-selection algorithm. |
| H10 | pp.242–244 | Narrow-scope accommodated definites under universal quantification and negation; father and king examples. |
| H11 | pp.245–246 (11)–(13) | Distinct local/global accommodation with a separating model, not a silently fixed global preference. |
| H12 | pp.218–220 C′ | False-context truth revision parameterized by relevance/repair; demonstrate why minimal structural constraints do not determine a unique truth prediction. |
| H13 | pp.247–250 | Prominence, remembered tentative cards and proxy licensing represented with explicit policy inputs; no invented recency threshold or claimed prediction of the unresolved contrasts. |
| H14 | pp.250–252 | Test the literal “identical satisfaction sets” claim for information-preserving accommodation; distinguish assignment-level information from unchanged possible-world content. |
| H15 | II.3 pp.105–111 | Indexed satisfaction semantics and existential closure; an explicit correspondence with a supported final-file fragment rather than an asserted equivalence of all versions. |
| H16 | II.4 pp.115–120 | World/assignment modal quantification, contextual accessibility and ordering, human necessity/possibility. |
| H17 | p.117 fn.8 | Record the source's own best-world existence assumption; demonstrate vacuity without best worlds rather than silently adding a limit assumption. |
| H18 | pp.121–129,251–252 | Distinguish modal from material conditionals, necessity from actuality, factive from nonfactive access, generic from universal predictions. Keep source-unsettled contextual choices explicit. |
| H19 | II.2 pp.86–101; II.5 pp.129–150 | Source-to-LF/construal and indexing constraints: inspect and record the implementation boundary; do not claim to have implemented an English parser or the full grammar from a semantic AST alone. |

## Encoding commitments

Use predicates for sets and relations, pointwise equivalence rather than equality
of functions, and natural-number indices with decidable symbol identity.
Finite-arity argument tuples must have their arity enforced. File domains need
not be enumerable; individual/world domains are not restricted to finite sets.
Semantic updates are recursively defined functions; their domain of felicity is
a separate proposition. This represents a partial mathematical function without
assuming a decision procedure for arbitrary semantic entailment.

Keep the constructive core distinct from classical metatheorems. Every added
logical assumption must be visible in the theorem statement or dependency audit.
No `Admitted`, semantic oracle masquerading as an implementation, or chosen
repair policy described as Heim's complete theory. Source-specified parameters
are legitimate parameters; an unresolved policy is a recorded missing prediction.

The final report must classify requirements as representation/infrastructure,
source assumptions, source clarifications/corrections, additional policy needed
for a unique prediction, or implementation still missing. A chosen encoding is
not evidence it was necessary. Tests must include false files, nonowners,
multiple donkeys, local scope, absent/contradictory descriptions, and source
boundary countermodels—not just successful examples.

Fresh compilation, all-theorem dependency queries, kernel rechecking and depth
probes are required before handoff. Add research files/records without changing
historical source-review snapshots or frozen P grades. No accepted source outcome,
push or deployment is implied by implementation alone.
