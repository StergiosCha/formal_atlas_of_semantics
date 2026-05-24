# Revisiting Formal Semantics Using Proof Assistants

Coq formalisations accompanying the paper *Revisiting formal semantics using proof assistants* (Stergios Chatzikyriakidis), written for Valeria de Paiva's Festschrift.

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

## Citation

If you use this code, please cite the accompanying paper:

> Chatzikyriakidis, Stergios. *Revisiting formal semantics using proof assistants*. In the Festschrift for Valeria de Paiva.

## License

MIT, see `LICENSE`.

## Acknowledgements

The Coq code development was written with assistance from Claude Opus-4.6/4.7-cowork; the proof assistant acts as the independent validator. 
