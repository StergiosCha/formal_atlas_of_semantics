# Hobbs — second-cohort source inventory, before implementation

Paper 101; frozen P2; baseline F1. Governed by
[stage A](cohort2_2026_09_13_protocol.md). No proposed obligation below has
been implemented or proved. Groups are linked parts of an account, not
independent trials or a denominator for a transfer score.

## Source identity gate and reading boundary

The selected file is `dynamic/Hobbs_1985_OnTheCoherenceAndStructure.pdf`,
SHA-256 `422ce067714e0865ec63f6b549cf96ac87e809d32fe98a79458bb9e96b618d9a`.
Its title is *On the Coherence and Structure of Discourse*, Jerry R. Hobbs.
All 36 pages, including references, were read from freshly generated OCR.
The original extracted text layer is unusable. Page citations below refer to
this local PDF's pages, which carry the same numbered body pagination.

**The filename/survey year does not authenticate this text as the 1985
version.** The undated local text cites Hovy 1988 on pp. 2 and 35, lists
Linde 1989 as forthcoming on p. 35, and refers to a next chapter on p. 34.
The exact revision/publication has not been identified. This inventory is
about the pinned local text only. Do not attribute a later implementation
outcome to the graded 1985 entry until a source-version match or a documented
version comparison resolves the issue. Keep the selected source and frozen
grade; do not silently substitute another text or retrospectively regrade it.

Visual checks covered title p. 1, Contrast/violated-expectation formulas and
algorithm example pp. 21–22, summary rules p. 25, and dating evidence p. 35.
OCR dropped important negations: (41a) is p(a) versus NOT p(b); (41b) uses
q(a) versus NOT q(b). Example (43) contrasts `INFO(M) > INFO(N)` with
`INFO(M) <= INFO(N)`, not a strict less-than branch. These corrections follow
the page images, not theoretical conjecture.

## H2-01 — Possible interpretation is not best interpretation

- **Claim, type, centrality:** PDF pp. 3–9. The six-component framework
  separates logical form, translation, world knowledge, deduction, possible
  interpretations and preference among them. Consistent combinations of
  discourse-problem solutions can be possible without being equally good.
  Deduction participates in understanding but is not all of understanding.
  This is the architecture on which the relation analyses depend.
- **Source cases and limits:** The book/index example permits identifying
  the index with that of the book, but an index of its first cited book is an
  alternative. Economy, salience and redundancy favor analyses without a fully
  specified numerical ranking. The text openly acknowledges on p. 9 that it
  supplies relevant knowledge and suppresses alternatives in worked analyses.
- **Possible obligation and limit:** Represent admissible interpretations and
  a separate preference relation; exhibit more than one possible interpretation
  without deriving a unique best one. Any winner must be conditional on explicit
  preference premises. A validity check is not an understanding algorithm.
- **Parameters versus additions:** Knowledge, logical forms and candidate
  solutions are legitimate parameters. An arbitrary winner, total ranking,
  fixed proof-cost objective or uniqueness axiom is an additional commitment.
  The example's idealized book-has-index formula is not an empirical universal
  about every real book; the surrounding prose qualifies its applicability.
- **Input versus prediction:** The source's knowledge and coreference options
  are inputs; an inference from them is conditional. Supplying the selected
  interpretation itself does not independently explain its selection.
- **Robustness:** Candidate: an explicitly fixed finite consequence relation
  represented by derivations versus its closure, with a correspondence proof.
  Equivalent best-interpretation encodings are not yet specified because the
  ranking theory itself is not supplied.

## H2-02 — Occasion is weaker than causation, stronger than chronology

- **Claim, type, centrality:** PDF pp. 9–11, definition (7). Occasion relates
  an inferred change to its initial or final state across adjacent segments.
  It is not mere temporal order or necessarily a causal connection. This is
  the primary relation in the initial narrative/procedural examples.
- **Source cases and limits:** A train arriving in Chicago and Reagan giving
  a press conference an hour later are not connected just by times; adding
  Reagan's being on the train can supply a relevant connection without the
  arrival causing the conference. Directions in (8) admit four compatible
  connections, not an exclusive single label.
- **Possible obligation and limit:** Encode the two state/change orientations
  with explicit witnesses and distinguish temporal precedence, Occasion and
  causation on a finite constructed example. Check compatibility of multiple
  relations. Witness existence does not establish a listener's preferred
  interpretation or an empirically adequate ontology of events.
- **Parameters versus additions:** Initial/final states, changes, inference
  premises and temporal facts are inputs. Equating Occasion with causation,
  selecting a unique label, or treating every state succession as relevant
  introduces assumptions absent from the definition.
- **Input versus prediction:** Reagan's presence on the train is added world
  knowledge, not inferred from the two original sentences alone.
- **Robustness:** Candidate: the same finite change described by initial/final
  projections versus a ternary state-change-state relation, with corresponding
  witnesses. Different notions of state identity would change semantics.

## H2-03 — Explanation of an event versus reason for an utterance

- **Claim, type, centrality:** PDF pp. 11–14, including (18). Explanation
  relates an event asserted in S1 to a cause, or possible cause, of the event
  asserted in S0. Evaluation concerns the utterance's role in a discourse-goal
  plan. Background uses a figure/ground relation. These distinctions block
  the reduction of all coherence to shared reference or undifferentiated cause.
- **Source cases and limits:** Foul humor, inadequate sleep and the blanket
  episode in (19) motivate reversed causal explanation. Reagan's having been
  a movie star and appointing Shultz share a referent but do not automatically
  supply suitable background. Causing a saying is not causing its content.
- **Possible obligation and limit:** Keep event content and utterance events
  distinct; test directionality of Explanation and show that shared reference
  alone does not entail a supplied background relation. A tagged distinction
  is representation only; it does not derive causation or discourse goals.
- **Parameters versus additions:** Causal/possible-causal knowledge, figure/
  ground judgments and goal plans are inputs. A fully effective plan recognizer,
  necessary causal laws, or an all-purpose relevance predicate adds theory.
- **Input versus prediction:** Causal links in the example must be sourced
  premises or labeled constructed assumptions, not passed off as new findings.
- **Robustness:** Not yet specified for the full plan/figure-ground accounts.
  Reversing cause arrows is a negative test, not an alternative faithful model.

## H2-04 — Parallel and Elaboration need informative shared content

- **Claim, type, centrality:** PDF pp. 15–20, definitions (22) and (30).
  Parallel infers a common predicate on similar corresponding arguments;
  Elaboration infers the same proposition from both segments and is treated
  as a special case. What makes a comparison good is partly left to the
  preference theory. These are central inference schemas, not complete
  context-free decision procedures.
- **Source cases and limits:** Program-initialization and directions examples
  illustrate common structure; the safe/combination example needs background
  knowledge and coreference. Elaboration deliberately includes mere repetition:
  requiring strictly new information would exclude a case the source retains.
- **Possible obligation and limit:** Express the schemas relative to admitted
  content/inferences; test the Elaboration specialization where the shared
  predicate and equal arguments are actually supplied. Probe the naïve formula
  “there exists P entailed by both”: unrestricted P allows True and makes every
  pair qualify. This is an encoding-sufficiency probe, not a refutation of an
  account that also appeals to specificity and interpretation preference.
- **Parameters versus additions:** Entailment, assertions and similarity
  judgments are parameters. Excluding tautologies, choosing a relevance domain,
  or setting a similarity threshold needs an explicit justification; a guard
  designed solely to obtain the desired example is not source-independent.
- **Input versus prediction:** Knowledge and aligned referents in worked cases
  are supplied. Inferring the common content from those premises is conditional;
  assigning the common content as input is a weaker representation-only test.
- **Robustness:** Candidate: a fixed finite set of admitted contents represented
  extensionally versus as a syntax with validated interpretation. Changing the
  admitted-content set or goodness criterion is a semantic change.

## H2-05 — Exemplification and Generalization have opposite orientations

- **Claim, type, centrality:** PDF pp. 20–21, (38) and following discussion.
  Exemplification relates a property of a set/category A to a member or subset
  a; Generalization reverses the orientation. This extends the common-structure
  account beyond identical or merely similar arguments.
- **Source cases and limits:** The list-reversal example uses input (A B C)
  and output (C B A). The definition allows a to be a member *or subset*, so
  silently choosing only individual membership narrows the stated schema.
- **Possible obligation and limit:** State and check the converse relationship
  under a common representation. Separate member and subset cases rather than
  blurring levels. The inverse property may be definition-level, not substantive
  evidence of transfer or successful understanding.
- **Parameters versus additions:** Domains, membership/subset relations and
  property lifting are inputs. A uniform predicate spanning individuals and
  collections needs an explicit typed or tagged design and interpretation.
- **Input versus prediction:** The list transformation can be computed if an
  independently specified reversal operation is supplied; knowing that it is
  the intended exemplification still depends on the discourse interpretation.
- **Robustness:** Candidate: disjoint member/subset witnesses versus a tagged
  instance relation that retains the same two cases, with a correspondence.

## H2-06 — Contrast need not make the retained assertions inconsistent

- **Claim, type, centrality:** PDF pp. 21–22, definition (41) and example (43).
  Contrast can use opposed predications with similar arguments, or a shared
  predication on arguments distinguished by an opposed property. It supports
  alternative branches in procedural discourse; a sequential reading can be
  wrong. Distinct arguments must not be silently identified.
- **Source cases and limits:** The algorithm example's complementary branches
  are greater-than and less-than-or-equal. Equality belongs in the second
  branch. Different probability thresholds in another example are contrasts
  without simply asserting P and not-P of the identical event.
- **Possible obligation and limit:** Encode both forms of (41) and check branch
  coverage/disjointness for the example's ordered values, including equality.
  Distinguish alternative-branch control flow from executing both branches.
  Arithmetic coverage is a restricted source-linked construction, not proof
  that natural-language contrast always has binary exhaustive branches.
- **Parameters versus additions:** Similarity, properties and the ordered
  comparison are inputs. Collapsing a and b, dropping negation, or replacing
  less-than-or-equal by less-than changes the content, not just notation.
- **Input versus prediction:** Explicit comparison conditions are source inputs;
  arithmetic coverage would be derived from the chosen order's laws.
- **Robustness:** Candidate: the same comparison represented by order predicates
  versus a three-way comparison result, proving correspondence at equality too.

## H2-07 — Violated expectation requires overridable inference

- **Claim, type, centrality:** PDF p. 22, (45)–(47). An expectation inferred
  from one segment conflicts with the following content; the expectation can
  be overridden. This important qualification is not exhausted by putting
  contradictory assertions into one monotonic knowledge base.
- **Source cases and limits:** The lawyer/honest example defeats a stereotype;
  it does not establish that lawyers are dishonest. The weak-but-interesting
  paper example connects contrast to acceptance considerations. Distinguish
  an expectation from retained asserted information.
- **Possible obligation and limit:** A future encoding must represent an
  expected P and an asserted not-P without validating arbitrary conclusions
  by explosion. Show override in a restricted example and preserve ordinary
  strict consequences separately. No complete default/revision calculus is
  specified by the chapter, so choosing one is a semantic addition.
- **Parameters versus additions:** Defeasible expectations and assertions are
  inputs. Priority, defeat, nonmonotonic consequence and update policy must be
  declared rather than attributed to the source's illustrative first-order
  notation. A lemma from inconsistent premises cannot count as success here.
- **Input versus prediction:** The source reports a stereotype; its use is a
  modeled expectation, not an endorsed fact about a group. The example outcome
  may follow conditionally from an explicit priority rule, not from logic alone.
- **Robustness:** No two source-determined default encodings are yet specified.
  Compare alternatives only after fixing the shared defeasible obligations;
  different priority policies are not mere representation changes.

## H2-08 — Recursive discourse structure is not always one global tree

- **Claim, type, centrality:** PDF pp. 23–24, 26–31. Recursive combination of
  related contiguous segments yields structures typically describable as one
  tree for well-organized texts. Conversation can have tangents, incomplete
  connections or forests. This is a qualified structural proposal, not a
  theorem that all discourse forms one tree.
- **Source cases and limits:** The narrative analyses show genre-sensitive
  organization. The envelope/dissertation comparison depends on similarity;
  conversation and the hitchhiking/Idaho example show local connections and
  ambiguous assertions without a guaranteed single global organization.
- **Possible obligation and limit:** Define finite contiguous-span combination
  and derive interval coverage for trees built by that rule. Retain forests
  and exhibit locally related clauses with no justified whole-text tree.
  Structural induction establishes properties of the constructed trees, not
  that a real discourse has the relations needed to construct one.
- **Parameters versus additions:** Clause order, segment relations, genre and
  chosen assertions are inputs. Universal connectedness, unique parsing or a
  fixed story grammar are extra commitments.
- **Input versus prediction:** Source analyses supply segmentation and relations;
  a validated tree is conditional on them unless they are independently derived.
- **Robustness:** Candidate: the same finite span tree represented recursively
  versus as nodes/edges with interval invariants; comparison must preserve labels
  and ambiguity, not discard inconvenient alternative parses.

## H2-09 — Summaries depend on relation and asserted content

- **Claim, type, centrality:** PDF pp. 24–26. Coordinate summaries use common
  content or property generalization; subordinate summaries track the dominant
  segment. Assertions need not coincide with main-verb predications. The author
  explicitly leaves the summary for Occasion uncertain. Summaries support the
  account of topics, so this underdetermination is central rather than cosmetic.
- **Source cases and limits:** The innocent-man example separates assertion
  from surface main verb. Explanation, exemplification and background have
  different dominant content; “but” usually privileges the second segment but
  has exceptions. For Occasion the text considers second assertion, change,
  or an abstract event, without settling the choice.
- **Possible obligation and limit:** Encode only explicitly scoped summary
  rules, keeping Occasion summary as a reported gap or separately labeled
  candidate policies. Do not obtain determinism by silently selecting one.
  Check any recursive summary against the stated relation and assertion inputs.
- **Parameters versus additions:** Resolved assertions and dominance information
  are parameters. A surface-verb extraction rule, total summary function or
  deterministic Occasion policy would add semantic commitments.
- **Input versus prediction:** Supplying an assertion/summary pair tests its
  representation, not automatic topic discovery from the sentence string.
- **Robustness:** Candidate Occasion policies are explicitly discussed by the
  author but not established as equivalent. Comparing them would measure
  unresolved semantic sensitivity, not certify robustness of a settled claim.

## H2-10 — Hypothesized knowledge needs validation beyond the worked text

- **Claim, type, centrality:** PDF pp. 31–34. The analysis method proceeds
  through segmentation, relations/summaries, hypothesized knowledge, then
  validation against a wider corpus. An elegant account of a single example
  cannot by itself establish that the knowledge is shared or explanatory.
  This is the chapter's explicit methodological conclusion.
- **Source cases and limits:** Connective substitutions such as then, because,
  or but can suggest relations but are informal clues, not definitions (p. 32).
  Further texts can require revising hypothesized knowledge. Missing: a held-
  out corpus and completed validation results for the full proposed framework.
- **Possible obligation and limit:** A future implementation can track which
  premises each interpretation uses and reject hidden assumptions. No internal
  proof can replace corpus evidence that those premises are appropriate.
- **Parameters versus additions:** Texts, annotations and hypothesized knowledge
  are inputs. Corpus selection, annotation criteria, fit measures and acceptance
  thresholds would be new methodological choices requiring advance disclosure.
- **Input versus prediction:** Reusing the explanatory example to validate its
  own hand-written premises is circular fitting, not the proposed wider test.
- **Robustness:** Not yet specified as an empirical validation design. The
  author's estimates of analysis time are not measurements of this campaign.

## Scope and next attempt

The inventory retains architecture, key relation families, structural
composition, summary gaps and corpus validation. It does not turn every
literary/programming example into a separate observation. Full knowledge
acquisition, discourse-goal recognition, pragmatic ranking, assertion recovery
and independently validated genre models remain uncovered.

Resolve the edition gate before beginning the planned paper-attributed
implementation, after Rosch. Then attempt explicit relation fragments with
H2-01's possible/best distinction, H2-04's tautology probe, H2-06's equality
case and H2-07's strict/default separation visible from the outset. A syntax
of relation names alone is not implementation of the explanatory theory.
Independent semantic review and alternative-encoding checks remain pending.
