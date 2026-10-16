# Handover

## 2026-10-16: separate Montague research publication

User authorized committing the accumulated research and deploying it as a
separate part of the app. `#/research` presents source-first PTQ, the
proof-theory workbench and the legacy correspondence without changing atlas
grades, outcome records, edges, aggregate counts or the live-library fingerprint.
All 53 Coq modules are published with exact bytes, declaration links and
recorded per-theorem dependency information. The separate checkpoint hashes
are checked at site build; all three checkers are mandatory in CI.

Research proofs are read-only/downloadable. The public worker does not yet
build their namespaces, so no research "Edit and run" action is advertised.
Existing atlas live Coq remains unchanged. A later worker rollout must preserve
the isolation and session checks and explicitly install those namespaces.

The new two-page overview and its renderer live in `deep/montague_ptq/`.
The source-first checkpoint is still 443 statements / 49 rejected fixtures;
core 173 / 23; legacy 76 / 14. All three isolated checkers and the 2,073-tree
reading report were rerun successfully on 16 October. Gallin equivalence,
independent semantic-review approval and exhaustive search remain unclaimed.
The research checkpoint can be published with these boundaries; older entries
describing incomplete exhaustive search are not a request to restart that task.

Publication verification: `atlas_data/test_research.py`,
`atlas_data/site/test_research.cjs` and `atlas_data/smoke_research.py` cover
source integrity, section separation, assumption display, downloads, browser
navigation and mobile layout. Inspect the deployment run for the final live
revision; this entry is preparation, not a claim that deployment has finished.

## 2026-10-10: redundant-wrapper normalization and local inverse proofs

This supersedes the normalization status in the previous entry. The current
checkpoint is 27 modules, 443 proved statements and 49 rejected negative
fixtures. Three additive modules were implemented; no pre-existing Coq
definitions, models or compiler rules were changed:

- `RenamingNormalization.v`: all-tree, all-model, both-policy equivalence
  for a structural normalizer that removes identity, unused-index and pure
  relabelling wrappers. Every successful tree has a no-larger merge-normal
  form; successful normalization is idempotent. Pure relabelling swaps
  internal binder names as well as leaves to avoid capture. Genuine index
  merges are retained. General freshening preserves quantifying-in meaning.
- `SurfaceInverse.v`: finite nonbare insertion and proper index-splitting
  inverses with soundness/completeness; the output-fresh binder convention
  preserves meanings and both policies. S3 relative-clause freshening is
  proved separately and does not rename the noun. Regressions check case
  preservation, forbidden empty/full splits, and a noun with a retained free
  pronoun index.
- `SearchRank.v`: the exact lexicographic triple used by the explorer is
  well founded. Both nonbare NP inverse bodies and genuine bare-merge inverse
  bodies strictly decrease it. This does not yet prove decrease of every
  parser branch or coverage of all branches.

The user asked to continue toward exhaustive classification of the same 20
strings. The requested classification is STILL NOT FINISHED. The precise
remaining task is a whole-search coverage bridge: combine normalization and
local inverses with every other grammar branch, rendering-mode propagation
and word tokenization, then connect the result to the finite certificate.
Do not restate the now-finished normalization obligation as still pending;
do not equate a well-founded measure with parser completeness. Neither the
Python filters nor its whole search have been Coq-certified.

The revised registry remains 20 strings / 27 sentence-specific classes.
All 2,073 discovered witnesses retain their checked all-admissible-model
classification. `verification.json` adds explicit true flags for the new
general results; whole-search completeness and exhaustive classification
remain false. See `deep/montague_ptq/READING_CLASSIFICATION.md` for the
expanded explanation. Checkpoints are recorded only through the isolated
checkers, not by editing their hashes by hand.

Final checks for this pass: isolated PTQ `--check` passed (443 statements,
49 negative fixtures); core and legacy `--check` passed unchanged (173/23
and 76/14). All kernel rechecks and PTQ assumption/signature audits passed.
The 2,073-witness report was regenerated and independently reproduced with
`--check-report`. All 24 workflow tests and 11 exploration tests passed.
`git diff --check` and the new Coq files' trailing-whitespace checks passed.

No commit, push, deployment, atlas promotion, email, external model call or
independent source approval is claimed. Preserve the pre-existing dirty worktree.

## 2026-10-10: missing belief reading proved; finite classification checked

User said "do it", asking for exhaustive reading classification of the fixed
20 PTQ strings. This task is NOT finished: the unrestricted theorem that every
successful grammar tree has an equivalent inverse-search representative is
still missing. Do not present the finite result as that theorem or expand the
finish line to Gallin/Henkin/MTT/TTR equivalence.

Verified checkpoint for that earlier pass: 24 modules, 348 proved statements, 38 rejected
negative fixtures, no global axiom dependencies. Five new modules:
`ReadingClassification.v`, `AdditionalReadings.v`, `PronounSupport.v`,
`GrammarRenaming.v`, `ReadingNormalization.v`. The pre-existing 19 Coq sources
were not edited in this pass.

Actual result: "Mary believes that John finds a unicorn and he eats it" has
an additional analysis with sentence conjunction OUTSIDE belief. Both literal
and amended surface policies generate it. An admissible model makes both old
readings true and the new reading false. The old no-unicorn model separates
the old dicto/re pair. `registered_belief_pair_not_exhaustive` refutes the
old pair under both policies. This corrects the project's candidate list;
it is not attributed to an assertion by Montague that there were exactly two.

The original `catalogue`, `reading_pairs` and amended catalogue are preserved.
`revised_catalogue` and `revised_reading_pairs` explicitly add the third reading:
20 strings, 27 analysis/formula pairs. All have combined surface/formula
certificates; `revised_candidates_pairwise_inequivalent` proves distinctness
WITHIN EACH sentence, conditional on BooleanTruth/FunExt for the separating
models. This is not a claim of 27 globally distinct meanings across sentences.

`explore_readings.py` proposes actual trees by inverse grammar operations.
`check_reading_exploration.py` emits and kernel-checks every witness, every
proposed computational grouping, and every group's all-admissible-model
equality to a candidate in the corresponding revised registry entry.
Result: 2,073 checked trees, 30 computational groups, 27 registered classes.
The three further identifications use `extensional_object_lifting` for the
appropriate TVs; seek/attitudes/control are not treated as extensional.
`reading_exploration.json` records the isolated-build result and source hashes.

The search omits identity/unused/pure relabelling loops and represents genuine
bare-pronoun merges by splitting a visible index class. Its normalization and
inverse coverage are not Coq-certified. Its rank assertions and finite output
are NOT a completeness proof. `search_completeness_proved` stays false.

Available general ingredients for the missing theorem:

- `support_is_visible` / `amended_support_is_visible`: semantic pronoun support
  appears in every successful realization's indexed tokens.
- `interpretation_depends_on_support`: agreement on that finite support implies
  equal denotation. Closed realized strings are assignment-independent.
- `arbitrarily_many_neutral_renamings`: arbitrary repeated bare wrappers around
  a closed realized sentence preserve its literal surface and meaning.
- `rename_tree_interpretation`, `rename_tree_surface`, `rename_tree_plan`:
  injective renaming commutes with semantics and BOTH surface policies for all
  S1-S17 trees. General non-injective capture avoidance remains a distinct issue.

Final isolated checks passed: PTQ 348, core 173, legacy 76 statements;
75 invalid fixtures rejected in total; all kernel checks passed; reading
report reproduced independently; 24 workflow tests and 11 exploration tests
passed; `git diff --check` passed. CI now requires the independent reading-certificate check and does
not automatically rerecord it.

Read `deep/montague_ptq/READING_CLASSIFICATION.md` for the full result, exact
counterexample, counts, code map and missing obligation. `FINISHING_REPORT.md`,
source map and READMEs are updated. No independent source approval is claimed.
No commit, push, deployment, atlas promotion or email was made.

## 2026-10-10: explicit surface amendment and all-tree safety completed

User said "go" after the concrete PTQ status summary. Implemented the
separately labelled present-inflection correction in `SurfaceAmendment.v`
and its general safety proof in `SurfaceAmendmentSafety.v`. No previous Coq
module changed: checked all 17 previous hashes before recording the new
checkpoint. Current total: 19 modules, 266 proved statements, 29 negative
fixtures, kernel-rechecked and assumption-audited.

There are now two explicit surface policies. `first_verb_only` is proved
identical to `Surface.surface` for EVERY tree. `coordinated_present` repairs
S4 present attachment by inflecting coordinated IV heads, propagating through
S10/S16 but stopping at control complements. S17 tense/sign is NOT distributed;
F10 missing-target failure remains. All 20 registered strings have analysis
witnesses; all 26 existing tree/formula pairs have combined surface/semantic
certificates for arbitrary admissible models and assignments.

`all_tree_amendment_erasure` proves equality of literal and amended outputs
after erasing verb-form fields, for every tree. Corollaries prove unchanged
lexical identity/order, pronoun indices, token counts and realization failure.
These are general proofs, not bounded searches. The old literal refutation
remains valid; the new coverage theorem concerns a different rendering policy.

Important: registered coverage is now proved, but all-reading exhaustiveness
is NOT. Do not turn the existential witness certificate into a universal
classification or claim independent source review. The scope fields in
`verification.json` distinguish both policies. No full PTQ adequacy, Gallin
equivalence or external-model adequacy was introduced.

Read `deep/montague_ptq/SURFACE_AMENDMENT.md` for the step-by-step proof guide.
The main report, source map, discrepancy report, review addendum and READMEs
are updated. No push, commit, deployment, atlas promotion or email was made.
Final isolated `--check` runs passed: PTQ 266, core 173 and legacy companion
76 proved statements; all 66 negative fixtures rejected; all three kernel
rechecks passed. All 23 workflow unit tests and `git diff --check` passed.
The historical entries below retain their earlier counts and boundaries.

## 2026-10-10: further implementation and a proved source-coverage obstruction

The user explicitly demanded finishing the remaining PTQ work, without
another partial-success handoff. Continued in `deep/montague_ptq/`.
The current checkpoint has 17 modules, 213 proved statements and 22 negative
fixtures. New files since the 92-statement checkpoint: `Scope.v`,
`FreshNames.v`, `ReadingForms.v`, `SurfaceInvariant.v`, `VacuousInsertion.v`.
`Surface.v` factors its unchanged bare-pronoun case into `bare_pronoun`.

Completed: both quantifier-scope reductions and a separating admissible
model; all 26 listed candidate analysis/formula correspondences as actual
IL terms; the exact editorial T3 least-even source-index procedure, bound
occurrence checking, literal replacement and intrinsic interpretation
correspondence. The raw candidate variable number is 4*k because x_m is
u_(2m,ic) and the note asks for even m. A further admissible model proves
that treating an absent F10 target as a no-op changes truth conditions.

Critical result: `printed_try_wish_has_no_analysis` and
`printed_wish_try_has_no_analysis` prove, for EVERY `tree ct`, that the two
printed p. 32 coordination sentences are not generated by the literal
surface rules. The proof is structural, not depth-bounded. It establishes
a token invariant, the allowed lexical vocabulary, and preservation through
rendering to words. `section4_generation_claim_refuted` refutes the blanket
claim that all listed section-4 strings have an analysis. Printed pp. 19
and 32 were visually checked. `SOURCE_DISCREPANCY.md` explains the proof.

Do not claim full PTQ adequacy or invent an exhaustive-reading theorem to
satisfy the user's demand. The unchanged literal positive coverage claim
is refuted. A surface amendment is a different explicit specification;
none was silently installed. Exhaustive classification for the other 18
strings remains uncertified. Independent source review is not claimed.
The distinction is source-rule coverage versus checked interpretation of
the listed candidate trees, not a claim that Montague semantics is impossible.

The checker now pins the new general theorem signatures and rejects
incorrect fresh-name choices, conflated scope formulas, omitted
admissibility, and asserted literal generation of the printed coordination.
Run `python3 deep/montague_ptq/check.py --check`.

Final regression run passed: PTQ 213 statements, core 173, legacy companion
76; all 59 negative fixtures rejected; all three kernel rechecks passed;
23 verification-workflow unit tests passed; `git diff --check` passed.

No older core/legacy Coq source or frozen review snapshot was changed.
No git commit, push, deployment, atlas outcome promotion or email was made.
Temporary incremental builds are in `/private/tmp/ptq-development.eArGVV`;
final verification uses the isolated checker, not that cache. Historical
entries below describe earlier checkpoints, not the latest result.

## 2026-10-10: source-first implementation pass closed

User asked to finish it off. The new PTQ branch now has 12 modules, 92 proved
statements and 17 rejected negative fixtures. Added `Named.v`,
`PostulateFormulas.v`, `Surface.v`, `Catalogue.v` and `Reductions.v` to the
previous seven-module checkpoint. The named and intrinsic evaluators are
proved to agree; all nine IL postulate families characterize exactly the
semantic `admissible` models. Ordinary determiner reductions, the first five
source examples, identity/predication, be extensionality, price truth
conditions and seek/try paraphrase are proved. The admissible example model
now also supports the about and belief nonreferential cases.

Surface catalogue: 18 section-4 sentences, 24 matching analysis witnesses,
plus two further canonical p. 32 analyses with an explicit inflection
discrepancy. Literal S4 inflects only the first verb, unlike those printed
examples. F10 non-bare-pronoun insertion returns None when no target exists;
that precondition is declared and needs source review. A translated candidate
tree with failed realization is not a reading of a surface sentence.

Five dicto analyses are true with no unicorns in the supplied admissible model;
eight listed re analyses require witnesses. Do not turn these finite facts
into an exhaustive-reading theorem. Remaining obligations: every printed
formula reduction (notably quantifier scope), unbounded all-analysis reading
classification, the exact editorial fresh-name procedure correspondence,
the surface convention questions, independent source review. See
`deep/montague_ptq/FINISHING_REPORT.md` and the updated `SOURCE_MAP.md`.

Final verification: all three isolated checkers passed (PTQ 92, core 173,
legacy companion 76 proved statements); all 54 negative fixtures rejected;
23 workflow tests passed. PTQ definitions and theorems were assumption-audited
and every module kernel-rechecked. Explicit BooleanTruth and FunExt premises
remain in the model. These are machine checks, not independent source review.

The previous checkpoint-7 mathematical sources and review snapshots are
unchanged. No email, deployment, push, commit or source-assessment promotion
has been performed for this pass. The historical section below describes
the earlier 44-statement source-first checkpoint, not the latest status.

## 2026-10-10: user authorizes source-first PTQ formalization

Latest instruction: formalizing Montague's actual paper is the objective,
not merely proving connections between encodings. A separate new branch
`deep/montague_ptq/` now reconstructs the primary source. The old checkpoint-7
Coq files and distributed review snapshots remain unchanged. The freeze
does not prohibit this newly authorized source-first work.

Primary PDF: `/Users/graogro/Dropbox/formalizing_formal_semantics/montague73.pdf`,
SHA256 `45ec6a0fa9bdac5c4fe92baf839aa90f60001a99a769a64fa7fa5c13f290b2e8`.
Consulted reprint pp. 17-34, including Thomason notes 9, 10, 12; formula pages
26 and 28 were visually checked. No independent review claimed.

IMPORTANT correction: the old deep encoding has the wrong IV/CN result type
and fixed-time necessity, both already recorded in its source audit. PTQ
has IV/CN type `intens e -> t` and necessity over all world/time pairs. The
previous explanation that fixed-time necessity was PTQ's choice was wrong.
The legacy preservation theorem remains valid for the old variant, not as
source adequacy. See the new `REVIEW_ADDENDUM.md`; do not share the old review
packet as a certificate that PTQ has been fully formalized.

New branch: seven modules, 44 named proved statements, all declarations
assumption-audited, 11 rejected invalid fixtures. It has all typed S1-S17
analysis rule families, a recursive T1-T17 compiler, source-correct Boolean
IL/models, independent analysis-tree interpretation and a theorem connecting
it to the evaluated translation, all nine semantic postulate families, a
constructed admissible model, compiled every/a reductions, nonreferential
unicorn and full two-premise temperature countermodels. BooleanTruth and
FunExt are explicit foundational model inputs; not global axioms.

Run `python3 deep/montague_ptq/check.py --check`. CI now requires this in
addition to the two old checkers. All three fresh kernel/audit checks passed;
23 workflow tests passed. No Coq source in the older branches was changed.
No commit, push, deployment, source-assessment promotion or email was made.

Full-paper obligations remain in `SOURCE_MAP.md`: surface F0-F15 operations,
named/intrinsic syntax correspondence and editorial capture conventions,
object-language formulas for the nine postulates with satisfaction equivalence,
remaining source examples and reading-exhaustiveness arguments. Continue
toward those source requirements, not another unrelated proof-theory layer.

## 2026-10-10: complete review handoff, not sent

The user asked to finish the review handoff for Robin and Rasmus, then
answered "none" when asked for recipient addresses. No email was sent and
none should be sent without new instructions. The mathematical freeze remains.

`deep/montague_core/prepare_review_dispatch.py` assembles the existing frozen
brief/report packet and walkthrough packet without changing their files,
checks their hashes against each other and the current Coq sources, and
reruns both checkers. The new review documents are `REVIEW_START_HERE.md`,
`REVIEW_RESPONSE.md` and `REVIEW_EMAIL.md`. The assembled packet is at
`/Users/graogro/Documents/Formal_Atlas_Montague_Review_Handoff_2026-10-10.zip`
with an unpacked sibling directory and a `.zip.sha256` checksum.

The packet includes the two-page brief, 128-page walkthrough, 53-page
technical report, all corresponding Word versions, unchanged checked source,
fresh check logs, a blank response form and an unsent covering email draft.
Fresh kernel checks: 173 core and 76 companion statements; all 37 negative
fixtures rejected. Separately, 22 `.github/tests` passed. Local document
links, PDF text, all frozen input hashes and ZIP contents were validated.
No mathematical extension, release, commit, push, deployment or reviewer
approval is claimed.

## 2026-10-09: detailed documentation only

The user requested an exhaustive, code-led walkthrough for Robin and Rasmus.
`deep/montague_core/WALKTHROUGH.md` and `WALKTHROUGH_SESSION.txt` explain the
unchanged checkpoint; `render_walkthrough.py` extracts exact source excerpts
from the frozen revised review packet, appends all 26 modules, and captures
fresh checks and the inspection session. Do not describe this as one person's
project. Mathematical implementation remains frozen pending review.

## 2026-10-08: Montague proof theory

Current instruction: freeze checkpoint 7 for scientific review. The user
approved a two-page review brief for Robin and Rasmus, with the long report
as supporting material. See `deep/montague_core/REVIEW_BRIEF.md`. Review source
fidelity, model assumptions and linguistic significance; correct identified
defects before any approved release. The mathematical extension suggestions
below are deferred, not an active implementation plan. No review endorsement,
tag, publication or email sending is claimed.

Latest: checkpoint 7 adds `ObservationBridge.v`, `ObservationExamples.v`,
`OBSERVATION_SPEC.md` and a nine-case `OBSERVATION_SUITE.json` in the companion.
The existing Boolean Ty2 and Prop explicit-index evaluators agree on a
certified base-quantified fragment under related lexicons and assignments.
Higher-order lambda/application are allowed only under the logical relation;
arbitrary truth/predicate quantification and equality are excluded. The
special encoded falsity case does not lift that quantifier restriction.
Main observation preservation needs no FunExt. Derivation consequence
transfer and finite paired examples do use explicit FunExt. Entity witness
observations retain the same entity, not just truth. All 36 new named proofs
have closed global contexts. No arbitrary model-class equivalence, full
legacy composition, tense comparison or source review is claimed.

The companion now has 76 statements in six files and 14 rejected fixtures.
Together with the unchanged core: 249 statements, 26 files, 37 rejected
fixtures. Both checkers remain mandatory. Run the companion checker below;
its inspection mode imports both observation modules. The cumulative report
is checkpoint 7, with section 17 and a complete 249-statement inventory.
Possible later work, now deferred: select reviewed readings and compose the
observation bridge with selected legacy translations and explicit conditions.
No deployment, atlas assessment or promotion is part of this checkpoint.

### Retained checkpoint-6 bridge history

Checkpoint 6 in `deep/montague_legacy/` was a separate four-file companion
with 40 proved statements and seven rejected fixtures. Run its own
`python3 deep/montague_legacy/check.py --check`; `--inspect` opens an isolated
Coq session. CI checks both branches. That checkpoint had 213 statements in 24 files.
The actual, unchanged `deep/PTQ_deep2.v` is hash-pinned and imported into the
isolated build. `legacy_open_preservation` covers every actual IL constructor
and assignment, including tense, equality and all 25 named lexical constructors.
Target truth is Prop, and indices retain World*Time. The proof uses explicit
FunExt and exactly the used old domain/lexical/time parameters, with per-statement
audits. No additional logical axioms, including propositional extensionality,
are used. Generic carrier transport follows equality of corresponding domains.
This is code-to-code preservation, not Montague source adequacy, Gallin
equivalence, a target proof calculus or a bridge to the Boolean model class.
The scoped target observation relation is now implemented in checkpoint 7;
an object calculus and full legacy-to-Boolean comparison remain open.
The core below is unchanged; its legacy-to-Boolean flags remain false.
Do not compile the corpus file in place under LegacyPTQ for later root-corpus
use: the namespaces differ. Use the isolated checker/inspection mode.
Its actual-legacy contract is unchanged. No deployment or promotion.

### Retained checkpoint-5 core history

The current bounded checkpoint and next research steps are in
[deep/montague_core/README.md](deep/montague_core/README.md).
Run `python3 deep/montague_core/check.py --check` with Coq 8.20.1.
Checkpoint 5 has 173 proved statements in 20 files and 23 rejected negative
fixtures. The three `IL*.v` modules define a world-only Boolean IL fragment,
independent implicit-index evaluation and a typed explicit-world translation.
`explicit_world_preservation` covers all typed terms under related assignments,
with FunExt explicit. Cancellation, index rigidity and 16 regressions test
binding and unsafe index-sensitive substitution. `IL_SPEC.md` states the
contract. This is not Gallin equivalence or a theorem about actual legacy IL.
No unrestricted IL beta/substitution rule or source proof calculus is added.
Next bridge the actual old syntax with explicit index/truth restrictions,
or prove a rigidity-aware source substitution theorem. Omitting tense alone
does not make the old World*Time intensions time-independent.
The five `Ty2*.v` modules add distinct world types, constant-domain
Boolean models, C-style derivations with soundness, an interpretation-preserving
C embedding and two-world countermodels. `INTENSIONALITY_SPEC.md` documents
the exact scope and the legacy IL audit. The embedding transports semantic
consequences; it is not yet a syntactic derivation translation, conservativity
or a legacy IL-to-Ty2 theorem. No tense or Henkin completeness is implemented.
`BooleanModels.v` proves soundness in a two-valued full internal
function-space interpretation. `BooleanFinite.v` constructs executable finite
models, including complete function domains. `BooleanEquality.v` implements
the book's Leibniz equality with finite-model reflection. `MODEL_SPEC.md`
records the source and assumption boundaries. Finite model construction
uses FunExt; the optional arbitrary-domain construction uses ClassicalDecision.
No external set-model adequacy or equivalence to the old Prop-valued model
class is claimed. The separate world layer has its own reflected quantifiers.
`Algebra.v` and `Structural.v` prove renaming/substitution
algebra, beta preservation and transformation of whole derivations without
semantic premises. `Contexts.v` independently defines an interleaved calculus
and proves its equivalence with split judgments. This is not yet adequacy for
the book's named typing judgments. `TECHNICAL_REPORT.md` explains each step.
This is an additive C/selected-Ty2 workbench, not a completed Montague/Ty2
formalization or a published atlas assessment. The original Prop-valued
soundness has FunExt and, in classical mode, ClassicalTruth. Boolean soundness
has FunExt and the model's quantifier-reflection contract, without an extra
ClassicalTruth argument. No global axiom dependencies, source-level promotion
or deployment is claimed. Keep the existing legacy and atlas files intact.

## Historical handover (2026-09-05, not current session ownership)

[.claude/handover/2026-09-05-inqb.md](.claude/handover/2026-09-05-inqb.md):
next action is `atlas/inquisitive/InqB.v`; DPL.v is finished but uncommitted and owned by a live Desktop session.
