# Revisiting Formal Semantics Using Proof Assistants

Coq formalisations accompanying the paper *Revisiting formal semantics using proof assistants* (Stergios Chatzikyriakidis). 

The paper argues that mechanisation in a proof assistant is a way to make formal-semantics theories precise and testable, and illustrates this with a case study of Montague's Intensional Logic (PTQ) and Kratzer's conversational backgrounds in Coq. The case study is run twice: once as a shallow embedding (Experiment A) and once as a deep embedding (Experiment B), so the two methodological choices can be compared side by side.

## Repository layout

```
shallow/   Experiment A — shallow embedding
deep/      Experiment B — deep embedding
extras/    other formalisations, not part of the paper
```

### `shallow/` — Experiment A

| File | Description |
| --- | --- |
| `MontagueFragment.v` | Extensional, intensional, and world--time Montague fragments. Provides the `MontagueWorldTime` module used by `kratzer2.v`. |
| `PTQ.v` | Shallow embedding of Montague (1973), "The Proper Treatment of Quantification in Ordinary English". Hybrid: deep analysis trees + shallow IL denotations. |
| `kratzer2.v` | Shallow embedding of Kratzer's conversational backgrounds. Contains the `kratzer_equals_montague` theorem proved by `reflexivity`, plus duality, Axiom K, monotonicity, necessitation, and disjunction distribution for the possibility operator. |

### `deep/` — Experiment B

| File | Description |
| --- | --- |
| `PTQ_deep2.v` | Deep embedding of Montague's Intensional Logic: `ILType` as an inductive type, IL expressions as a GADT indexed by context and type, full `eval` interpretation function, temperature-puzzle countermodel section. |
| `kratzer_deep2.v` | Kratzer's modal operators built as semantic functions over the denotations of deep IL expressions. Re-proves the Kratzer--Montague equivalence (still by `reflexivity`) and the S5 axioms on top of the deep IL. |
| `theorems_deep_PTQ.v` | Metatheorems about the deep IL: every-to-some, the-entails-a, relative-clause restriction, T and S4 axioms for the box, extensional collapse, beta-soundness, up/down identity, temperature non-entailment. |

### `extras/`

Additional Coq formalisations from a broader research programme on type-theoretic and event semantics, Champollion-style event semantics, Dowty's thematic proto-roles, Lakoff prototypes, file-change-style fragments, polydefinites, presupposition projection, and so on. These are not part of the paper's case study but are kept here for reference and reuse.

## Building

A `_CoqProject` is provided. With Coq (8.16 or later) installed:

```bash
coq_makefile -f _CoqProject -o Makefile
make
```

To build only one experiment in dependency order:

```bash
coqc shallow/MontagueFragment.v
coqc shallow/PTQ.v
coqc shallow/kratzer2.v
```

```bash
coqc deep/PTQ_deep2.v
coqc deep/kratzer_deep2.v
coqc deep/theorems_deep_PTQ.v
```

The later FORMAL-ATLAS work lives in `atlas/` with records and the local site
in `atlas_data/`. For the source-checked TTR, MTT, Ranta and DTS comparisons,
see [the comparison audit](atlas_data/audits/ttr_comparison.md).
It documents the explicit TTR model layer, the limited witness-erasing
TTR-to-MTT comparison, and the noun/context translations required by DTS.
The audit also lists the source passages read and reproducible build commands.
The [September 13 revision](atlas_data/audits/revision_2026_09_13.md) adds
typed DTS resolution, four shared constructions, and a prospectively selected
[P1/P2/P3 pilot](atlas_data/campaigns/pilot_2026_09_13_results.md).
Incomplete source coverage is reported as unassessed, not as evidence that
the theory requires major restructuring.

The subsequent [P0/P1/P2 coverage campaign](atlas_data/campaigns/tiers_2026_09_13_results.md)
adds bounded Derrida, Austin and Horn pilots. The source-to-code ledger separates
direct logical fragments from added illustrative models and uncovered claims.
All three remain F3/unassessed; passing Coq does not verify the whole sources.

The [claim-level comparison](atlas_data/campaigns/claim_comparison_2026_09_13.md)
separates represented examples, source-linked fragments, added semantic commitments
and uncovered claims across those three pilots plus Grice and Tarski. Open
**Claim comparison** on the local atlas site; these qualitative profiles do not
change evidence levels or establish a tier gradient.

The [second cohort](atlas_data/campaigns/cohort2_2026_09_13.md) freezes
Spivak/Rosch/Hobbs source inventories before implementation. Its first
[Rosch pilot](atlas_data/campaigns/rosch_2026_09_13_results.md) checks finite
cue validity and membership/typicality separation. Rosch remains P1 and is
reported as F3/unassessed: the checked fragment does not derive a psychological
basic level or validate prototype effects. Hobbs's local source version needs
identification before its implementation; Spivak has not been implemented.

## Citation

If you use this code, please cite the accompanying paper:

> Chatzikyriakidis, Stergios. *Revisiting formal semantics using proof assistants*. In progress.

## License

MIT, see `LICENSE`.
