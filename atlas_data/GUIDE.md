# FORMAL-ATLAS reading guide: from a (semi-)formal paper to a verifiable file

Companion to `RUBRIC.md`. The rubric judges a FINISHED formalization; this
guide is the protocol for READING a paper — especially a semi-formal or
informal one — and deciding what a Coq file about it should even say. It is
written for a working semanticist, not a proof engineer. Worked micro-example
at the end (Giannakidou-style (non)veridicality).

## 0. The one-sentence method

Separate what the paper DEFINES from what it CLAIMS from what it merely
GLOSSES; formalize the definitions, prove or refute the claims, and record the
glosses as the untranslatable remainder — the remainder is a finding, not a
failure.

## 1. First pass: inventory (no Coq yet)

Produce four lists, with page references:

1. **Ontology** — what kinds of things does the paper quantify over?
   (worlds, times, events, degrees, individuals, contexts, speakers,
   alternatives, probabilities...) Every unexplained kind becomes a Coq
   `Variable ... : Type` — and the paper's SILENCE about its structure is
   your first datum. If the paper never says whether worlds are a set or a
   frame, the file takes a bare Type and any theorem needing more will
   surface the hidden assumption (rubric: NEEDS_ASSUMPTION).
2. **Definitions** — everything of the form "we say X is Y iff Z", tables,
   type assignments, semantic clauses. These translate nearly mechanically;
   grade each `exact / simplified / changed` per the rubric as you go.
3. **Claims** — everything the paper asserts follows: numbered facts,
   "clearly", "note that", "as the reader can verify", predictions
   ("correctly predicts that (12b) is out"). Each becomes a candidate
   theorem — INCLUDING the ones inside prose. In semi-formal papers the
   load-bearing claims are usually unnumbered.
4. **Glosses** — appeals to pragmatics, processing, "speakers tend to",
   crosslinguistic tendencies, analogies. NOT formalizable as stated; they
   go to the file header's NOT FORMALIZED block with the reason. Never
   silently promote a gloss to an axiom.

## 2. Second pass: sharpening (the semi-formal gap)

For each claim, ask the three sharpening questions:

- **Quantifier scope.** "Negative polarity items are licensed in downward
  entailing contexts" — for ALL NPIs? all DE contexts? Write both readings
  as Coq statements; often only one is provable and THAT disambiguation is a
  result the paper itself never states.
- **Modality of the claim.** Is it a mathematical consequence of the
  definitions (theorem), an empirical generalization (becomes a PREDICATE
  the theory imposes on lexica — formalize as "for every lexicon satisfying
  the licensing condition, ..."), or an analytical choice (becomes a
  definition, not a theorem)?
- **The domain of examples.** Papers argue from ~10 sentences. The file
  should contain those sentences as concrete instances (the paper's (12a),
  (12b) as Coq terms) and the general claim separately; when the general
  claim fails, the instances usually still go through — and the gap between
  them is the paper's real content (cf. DPL.v's d34_refuted: the printed
  law is false, the motivating instances are fine).

## 3. Encoding decisions (before writing proofs)

Follow the atlas conventions, which exist mostly to keep evidence clean:

- **Zero axioms.** Lexicon and domains are Section Variables; empirical
  side conditions are hypotheses of the theorems that need them. A
  `Parameter`/`Axiom` poisons every `Print Assumptions` downstream. (The
  rubric §3 admits classical/extensionality axioms when the source's
  metalanguage is set theory — document them in the header.)
- **Negative claims are existence theorems.** "X does not follow" is
  `exists <small model>, X-holds-here /\ counterexample` over `bool`/`unit`
  — axiom-free and checkable, never an `Admitted` or a remark.
- **Absences are data.** If the theory provides no veridicality inference
  for "allege", prove the countermodel that shows none is derivable
  (MTT.v's noncommittal_witness) rather than leaving silence.
- **Grade the distance while translating** (`exact/simplified/changed`),
  and write the artifact classes as you hit them; retrofitting them later
  loses the information.

## 4. What "verified" means for an informal paper

Not "the paper is true" — rather, a partition of its content into:

- **PROVED**: claims that follow from the paper's own definitions
  (theorems, `Print Assumptions` clean per rubric §3);
- **REFUTED**: claims false as printed, with countermodels (these are
  publishable findings — see DPL.v's misprints);
- **NEEDS_ASSUMPTION**: provable only with a premise the paper does not
  state — the formalization has NAMED a hidden premise, which is the
  single most valuable output for a semi-formal source;
- **NOT STATABLE**: glosses and meta-level claims, recorded with reasons.

The record (records/*.json) and the graded edges (edges/*.json) then place
the paper in the atlas: how much of it is theorem-shaped at all is itself
the formalizability verdict.

## 5. Worked micro-example: (non)veridicality (Giannakidou-style)

A typical semi-formal target: rich prose, one crisp core.

1. Ontology: propositional operators F (sentence embedders); a notion of
   truth. Coq: `Variable F : Prop -> Prop` (or context-relativized
   `F : (W -> Prop) -> W -> Prop` if the paper relativizes — read which!).
2. Definitions (crisp core, translate exactly):
   - veridical:      `veridical F := forall p, F p -> p`
   - nonveridical:   `~ veridical F` — or, sharper and closer to intent,
     the existence form `exists p, F p /\ ~ p` witnessed per operator;
   - antiveridical:  `antiveridical F := forall p, F p -> ~ p`.
3. Claims to prove: "know/factives are veridical" (theorem, given the
   factive meaning postulate — which the formalization forces you to
   state: THAT is the hidden-premise finding); "negation is antiveridical"
   (theorem); "'perhaps' is nonveridical" (existence countermodel);
   "antiveridical implies nonveridical (given a consistent F)" (theorem —
   and the consistency side condition is another named premise).
4. Claims to re-type: "NPIs are licensed only in nonveridical contexts" is
   NOT a theorem about the semantics — it is a constraint on lexica.
   Formalize as a definition (`licenses F NPI := ...`) plus per-item
   instances; its universal form is an empirical generalization the file
   records, not proves.
5. Glosses (header, NOT FORMALIZED): rescuing/expressive uses, speaker
   commitment as attitude, diachrony.

The output: a small axiom-free file where the veridicality calculus is
proved, two hidden premises are named (factivity postulate; operator
consistency), the licensing claim is correctly re-typed as empirical, and
the prose remainder is documented. That is what "formally verifying" a
semi-formal paper means in this project.
