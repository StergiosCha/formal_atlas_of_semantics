# Rosch — second-cohort source inventory, before implementation

Paper 122; frozen P1; baseline F1. This inventory follows
[stage A](cohort2_2026_09_13_protocol.md). All obligations below are prospective:
no new definitions, proofs, empirical replications or transfer verdicts exist.
Target groups are not independent observations or a success-rate denominator.

## Source and reading boundary

Eleanor Rosch, *Principles of Categorization* (1978), local file
`foundations/Rosch_1978_PrinciplesOfCategorization.pdf`, SHA-256
`45e33ffdfe2d79f5c63f1d70b28bcc5c8e6e72f3b761c17930a8af4bc50d8fbe`.
The header identifies the chapter in Rosch and Lloyd, *Cognition and
Categorization*, original pp. 27–48. The local PDF is a reformatted 25-page
text, not a facsimile of that pagination. **Every page citation below is a
local PDF page**, not an inferred original page. All 25 pages, including
references, were read. Definitions on p. 5 and constraints on p. 16 were
also checked visually. Some typographical errors are in the local PDF itself.

The chapter explains category systems: vertical inclusiveness/basic levels,
horizontal typicality, their ecological and cognitive motivations, and limits
of existing accounts. It explicitly does not offer a general processing or
developmental algorithm. Despite the frozen P1 grade, it contains a conditional-
probability definition and discusses several formal measures. Record this
fragment-level heterogeneity; do not change the grade or erase the mathematics
to manufacture a tier contrast.

## R2-01 — Cognitive economy and perceived-world structure

- **Claim, type, centrality:** PDF pp. 1–4, 22. Two programmatic principles
  motivate the account: useful information with limited cognitive effort, and
  exploitation of correlated structure in the *perceived* world. They are not
  a specified numerical optimization problem. They frame the chapter's thesis.
- **Source cases and limits:** Wings co-occur with feathers more than with fur;
  chair-like structure relates to possible actions. The world perceived by an
  organism is not an arbitrary equiprobable combination of attributes, but nor
  is it a fully specified world independent of perceivers and culture.
- **Possible obligation and limit:** A finite illustration could distinguish
  correlated from independent features. It would illustrate a premise, not
  prove an optimal category system or the psychological economy of a subject.
  No source-faithful global objective function is fixed here.
- **Parameters versus additions:** Objects, attributes and observed frequencies
  are ordinary inputs. Choosing a loss function, information/effort trade-off,
  or optimization algorithm would add substantive commitments.
- **Input versus prediction:** Feature data and costs would be inputs; examples
  assigned those data are not independently predicted by the construction.
- **Robustness:** Not yet specified for the programmatic claim. Comparing two
  arbitrary utility functions would change the theory being tested.

## R2-02 — Basic level as the most inclusive level with shared structure

- **Claim, type, centrality:** PDF pp. 4–10. The proposed basic level is the
  most inclusive level at which bundles of perceptual and functional properties
  are shared. Common attributes, motor programs, shape similarity and averaged-
  shape identification provide converging empirical operationalizations. This
  is the central vertical-dimension proposal, not an unconditional theorem
  about every taxonomy or person.
- **Source cases and limits:** Furniture/chair/kitchen-chair exemplifies the
  intended hierarchy. The biological hierarchies did not place the tested
  subjects' basic level where folk-taxonomic expectations initially suggested;
  tree rather than a more specific expected level can emerge. Knowledge and
  experience matter (pp. 7, 9). Do not discard this source countercase.
- **Possible obligation and limit:** Given a finite inclusion taxonomy and
  independently supplied sharing criterion, identify qualifying nodes on its
  branches and ask when they determine a common level/cut. Multiple categories
  at a basic level are not a failure of uniqueness: do not confuse one level
  with one category. A constructed case with incompatible branchwise levels
  would test an extra uniform-level assumption, not refute the empirical
  account. The source already assumes unique immediate parent categories
  (p. 5); that tree-like organization is not an invented source omission.
- **Parameters versus additions:** Taxonomy and measurements are inputs.
  Thresholds, aggregation across the four measures, tie-breaking and fixed
  observer-independent levels are additional choices not provided by the text.
- **Input versus prediction:** Encoding chair as basic by a flag is only a
  representation. A prediction requires independently specified feature data,
  selection rules and a comparison with subject judgments.
- **Robustness:** Candidate: the same fixed finite hierarchy represented by
  inclusion predicates versus an explicit order, with a correspondence proof.
  Changing the sharing criterion would be a semantic sensitivity test instead.

## R2-03 — Cue validity and the proposed basic-level maximum

- **Claim, type, centrality:** PDF pp. 5–6. Cue validity is the conditional
  probability of a category given a cue; total category cue validity sums
  validities of attributes of that category. Rosch uses discontinuities in
  shared attribute bundles to motivate a basic-level maximum. Category
  resemblance is another proposed formulation, not an identical definition.
  This is a central proposed explanation of R2-02, conditional on how category
  attributes and contrasts are determined.
- **Source cases and limits:** Chair-like common attributes provide the
  intended contrast with heterogeneous furniture and overly specific chairs.
  The passage supplies no numerical frequency table from which the claimed
  maximum could independently be recomputed. Missing: a numerical positive/
  negative pair for the full measure.
- **Possible obligation and limit:** First express cue validity on a finite
  probability model, with nonzero cue probability explicit. Prospectively test
  the following *encoding boundary*: for nested categories C contained in D,
  holding the cue set and nonnegative weights fixed makes each P(C | cue) no
  greater than P(D | cue), hence also their fixed-weight sum. This is a proposed
  mathematical check, not a completed proof or a refutation of Rosch: her
  category-specific attribute sets must not silently become a common pool.
  Any interior-maximum construction must expose the attribute-selection or
  contrast assumptions that make it possible.
- **Parameters versus additions:** Category membership, observations, cue
  predicates and their relevance to each category are inputs. Identical cue
  pools across levels, learned feature selection, arbitrary weights or a
  replacement resemblance metric are substantive choices. Record zero-cue
  treatment rather than hiding division by zero.
- **Input versus prediction:** Synthetic counts are illustrative inputs. A
  calculated maximum conditional on chosen counts is not a replication of the
  chapter's experiments or proof of a psychologically privileged level.
- **Robustness:** Candidate: finite event probabilities versus normalized
  frequency counts on the same dataset, keeping category-specific attributes
  fixed. Cue validity versus Tversky-style resemblance compares different
  substantive proposals, not two encodings of one measure.

## R2-04 — Graded typicality without a unique prototype object

- **Claim, type, centrality:** PDF pp. 10–16. Natural categories exhibit graded
  goodness-of-example judgments. A prototype can be shorthand for such
  judgments, not a unique stored object or a precise boundary. Within-category
  representativeness and differentiation from contrasting categories must be
  distinguished. This is the central horizontal-dimension account.
- **Source cases and limits:** Robin versus penguin and the qualification
  “technically” a bird distinguish typicality from membership. Sparrows versus
  turkeys fit a perching/twittering context differently. Artificial stimuli can
  separate dimensions that correlate in natural categories; no single literal
  natural-category prototype is thereby identified.
- **Possible obligation and limit:** Represent membership and a typicality
  ordering separately; exhibit members differing in typicality and a ranking
  without a unique maximizer. These are consistency/separation illustrations,
  not proof that a supplied ranking matches human judgments.
- **Parameters versus additions:** Rated judgments, comparison categories and
  context are inputs. A metric, unique centroid, nearest-prototype decision
  rule or fixed membership threshold would be substantive additions.
- **Input versus prediction:** Robin/penguin ranks would be sourced qualitative
  constraints, not model-generated experimental outcomes. Numerical distances
  would need separate justification and labeling as constructed values.
- **Robustness:** Candidate: the same finite weak ordering represented directly
  versus by order-preserving scores. Do not identify ordinal preservation with
  preservation of distances, processing times or fuzzy membership degrees.

## R2-05 — Prototype effects constrain, but do not determine, mechanisms

- **Claim, type, centrality:** PDF pp. 13–16, especially 15–16. Findings about
  typicality bear on processing, representation and learning, but are not by
  themselves one theory of any of these. The explicit qualification prevents
  a misreading of the chapter's overall explanatory achievement.
- **Source cases and limits:** Reaction-time, learning, output-order and
  priming effects motivate constraints. Feature lists, structural descriptions
  and templates are among possible representations; multiple learning accounts
  are discussed. Their mention is not an endorsement of interchangeable full
  models. The criticism of necessary-and-sufficient feature accounts is
  qualified, not a proved impossibility theorem for every such account.
- **Possible obligation and limit:** A future underdetermination witness could
  give two explicitly different mechanisms satisfying a precisely enumerated
  subset of observational constraints. It must state which constraints were
  omitted; fitting an invented single ranking cannot establish equivalence
  on all the evidence cited by Rosch.
- **Parameters versus additions:** The observational signature is an input.
  A new transition system, latent representation or learning update is an
  added model, not Rosch's hidden algorithm recovered from the prose.
- **Input versus prediction:** Reproducing constraints built into both models
  is fitting/illustration; independently held-out observations would be needed
  for empirical discrimination.
- **Robustness:** Two suitable source-defensible mechanisms are not yet fixed.
  This is an underdetermination test, distinct from representation-preserving
  robustness of a single mechanism.

## R2-06 — Context changes what counts as basic or typical

- **Claim, type, centrality:** PDF p. 18, with pp. 12–16. Category judgments
  are context-sensitive; “most situations” does not mean every situation.
  Apparently unspecified experimental context is normally interpreted, not
  literally absent. This qualifies R2-02 and R2-04.
- **Source cases and limits:** Shopping for furniture can make a more specific
  chair label appropriate; typical animals differ between an African-animal
  frame and an American-pet frame. These examples do not prescribe a universal
  numerical context-update law.
- **Possible obligation and limit:** A context-indexed hierarchy/ranking may
  exhibit a change while category membership remains separately represented.
  Proving a change after supplying two changed tables is only an illustration,
  not an explanation or prediction of context effects.
- **Parameters versus additions:** Context and judgments are inputs. A fixed
  context space, salience dynamics or quantitative update is additional theory.
- **Input versus prediction:** Source qualitative contrasts may be inputs;
  computed consequences must be distinguished from those supplied contrasts.
- **Robustness:** Not yet specified for a cognitive context model; a mere
  relabeling of context keys would be an engineering check only.

## R2-07 — Attributes are not all prior to categorization

- **Claim, type, centrality:** PDF pp. 17–18. Some attributes themselves depend
  on categories and cultural practice. The existing account does not explain
  all origins of category systems. This is a central limit on R2-01–03, not
  permission to treat a feature vocabulary as a neutral universal inventory.
- **Source cases and limits:** Seat presupposes chair-like organization;
  a piano is large relative to furniture, not buildings; eating-on is a
  culturally functional attribute of a table. These do not imply every
  attribute is arbitrarily created or that perceived structure is irrelevant.
- **Possible obligation and limit:** No origin theorem is specified. An
  illustration could distinguish raw measurements from context/category-
  relative predicates, but would not explain their historical acquisition.
- **Parameters versus additions:** Measurement and comparison classes are
  inputs; a learning process generating the attributes is a substantive addition.
- **Input versus prediction:** Assigning category-relative predicates encodes
  the distinction; it does not derive the emergence of those predicates.
- **Robustness:** Not yet specified. Keep this central limitation visible even
  if the first implementation assumes a fixed feature vocabulary.

## R2-08 — Tentative extension from objects to events and scripts

- **Claim, type, centrality:** PDF pp. 19–22. An explicitly preliminary event/
  script extension connects remembered event units, abstraction levels and
  basic objects in activities. It extends the program but is less established
  than the object-category evidence; preserve that modality.
- **Source cases and limits:** Accounts of daily events retain useful units
  despite changing recall extent; narratives with overly general descriptions
  are uninformative and excessively specific descriptions can become comic.
  These are not a complete event grammar or a universal comprehension law.
- **Possible obligation and limit:** No source-determined event-selection
  algorithm is identified. A finite event hierarchy could illustrate the
  analogy but could not establish the reported memory/comprehension findings.
- **Parameters versus additions:** Event boundaries, scripts and judgments are
  inputs. A compositional event ontology or optimization rule would add theory.
- **Input versus prediction:** Replaying the described narratives is input
  encoding unless selection/comprehension is independently predicted.
- **Robustness:** Not yet specified; keep this extension as a tentative central
  remainder if no defensible formal target is found.

## Scope and next attempt

This inventory covers the main explanatory program and its self-limitations,
not every cited experiment as a separate target. Experimental datasets,
cross-cultural generalization, learning and processing models remain outside
the present evidence. No cited work has been independently replicated or fully
read merely because it is in the bibliography.

The next bounded attempt should start with R2-03's exact probability definition
and encoding-boundary test, then R2-04's membership/typicality distinction.
Every other target must still receive an explicit disposition. A successful
fragment will not establish that Rosch's theory as a whole transfers as-is.
Independent semantic review and alternative-encoding checks remain pending.
