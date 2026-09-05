# FORMAL-ATLAS assessment rubric

This is the criterion applied to every entry of the atlas. Its purpose is to make
"mechanizable" an evidenced judgement rather than an impression: every verdict below
must point at a Coq file, a theorem name, a `Print Assumptions` output, or a page of
the source. A verdict without evidence is not a verdict.

## 1. Unit of assessment

The unit is a **source theory** as presented in one or more primary texts (a paper, a
book chapter, a dissertation), and the **Coq file(s)** that attempt to formalize it.
Each atlas record names both. A source with no Coq file carries only the survey
category (§5) and is marked *unassessed*; nothing in §2–§4 applies to it until code exists.

## 2. Faithfulness of a formalization to its source

Answers: *does this Coq file formalize what the source says?* Judged on the mapping
from source constructs to Coq constructs. Every major definition of the source that
the file claims to cover is classified as one of:

| Match | Meaning |
|---|---|
| `exact` | the Coq definition is the source definition up to notation |
| `simplified` | a special case or restriction (e.g. finite domains, one world, no time index) that the source does not impose; the theorems still concern the source's objects |
| `changed` | a different definition that the file substitutes for the source's (e.g. lists for sets, relations for functions) in a way that alters which claims are provable |
| `added` | machinery with no counterpart in the source (helper lemmas, decidability instances) |
| `missing` | a construct the source relies on that the file omits |

Every theorem is classified as verifying a *named source claim* (fact, theorem, worked
example, numbered inference) or as *new*.

Verdicts:

- **faithful** — every core definition is `exact` or `simplified` with the simplification
  stated, and the headline claims of the source are proved as theorems.
- **partial** — the core is faithful but headline claims are missing, or at least one
  core definition is `changed`.
- **unfaithful** — the file's theorems concern objects that are not the source's, or a
  headline claim is stated but not established.
- **not_applicable** — infrastructure files with no source.

## 3. Proof integrity

A theorem counts only if it ends in `Qed` and its `Print Assumptions` output lists
nothing beyond: (a) declared *signature* parameters (types, constants, functions with
no propositional content); (b) axioms the **source itself** takes as axioms, each
documented with the source reference; (c) the standard extensionality and classical
principles of Coq's own library — excluded middle (`Classical`), functional
extensionality, propositional extensionality, and set extensionality
(`Extensionality_Ensembles`) — when documented in the file header. These are admitted
because they are consistent with the calculus, are used by the source theories'
set-theoretic metalanguage without comment, and their use is itself recorded as evidence
(a theory whose every equation needs propositional extensionality is telling us it
identifies propositions with truth conditions). An `Admitted` theorem counts as a *finding*, never as
a result, and must carry one of three classifications:

- **FALSE** — the statement is false as written (countermodel given);
- **NEEDS_ASSUMPTION** — provable only with an assumption the source does not state
  (this is evidence about the theory: it names a hidden premise);
- **HARD** — believed true, proof not completed (this is evidence about us, not the theory).

Trivial theorems (true by unfolding, or with inconsistent hypotheses) are excluded
from counts by the verifier.

## 4. Four-point determination of the source theory

Answers: *how does the theory itself fare under mechanization?* It is a property of the
theory, evidenced by its best formalization, not a property of one file.

| Determination | Criterion |
|---|---|
| **1 as-is** | A faithful formalization exists whose core definitions are all `exact`, whose headline claims are proved, with no propositional axioms beyond §3(b–c), and whose encoding artifacts (§4.1) are at most class (iv). |
| **2 slight modification** | A faithful formalization exists but needed `simplified` definitions or a documented extra assumption (NEEDS_ASSUMPTION) that does not change the theory's predictions; artifacts at most classes (iii)–(v). |
| **3 major restructuring** | Only a `partial` formalization exists: a core definition had to be `changed`, or a headline claim could only be recovered after re-founding part of the theory (e.g. replacing an informally specified operation by an explicit algorithm the source does not give). Typically class (i) or (ii) artifacts. |
| **4 cannot** | The resistance is foundational and is *diagnosed*: the source relies on an object or operation that is either inconsistent with type theory as stated (class i/ii artifacts with no workaround preserving the theory) or not specified precisely enough to admit any definition (the file must document the precise point of underspecification). "We did not manage" is not "cannot". |
| n/a | no source theory (infrastructure). |

### 4.1 Encoding artifact classes

Recorded for every file (typology from the March 2026 comparative-study proposal):

| Class | Name | What it reveals about the theory |
|---|---|---|
| (i) | strict-positivity violation | its central relation is circular in a way type theory rejects |
| (ii) | universe-level / type–value collapse | it identifies types with values or quantifies over all types |
| (iii) | computational opacity | an operation that should compute becomes opaque under encoding (e.g. reals, exp/log) |
| (iv) | missing native structure | it needs machinery the substrate lacks (coercive subtyping, proof nets, categories) |
| (v) | decidability gap | it assumes decidable equality/membership that cannot be guaranteed |

## 5. Survey category (papers without code)

The 200-paper survey's categories A–D are *predictions*, not determinations. They are
mapped provisionally to 1–4 and displayed in a different colour until a formalization
exists; a completed formalization replaces the prediction with a determination, and
the atlas records where the two disagree (these disagreements are themselves findings).

## 6. Independent verification

Every record is checked by a second, adversarial pass that reads the source and the
Coq file independently, recompiles, reruns `Print Assumptions`, and is instructed to
dispute when uncertain. The verifier's revised verdict is the one displayed; the
original is retained and the dispute is listed.
