# Revisiting Formal Semantics Using Proof Assistants

Coq formalisations accompanying the paper *Revisiting formal semantics using proof assistants* (Stergios Chatzikyriakidis), written for Valeria de Paiva's Festschrift.

The paper argues that mechanisation in a proof assistant is a way to make formal-semantics theories precise and testable, and illustrates this with a case study of Montague's Intensional Logic (PTQ) and Kratzer's conversational backgrounds in Coq, in both shallow and deep embeddings.

## Files used in the paper

The central case study uses six files:

| File | Description |
| --- | --- |
| `MontagueFragment.v` | Extensional, intensional, and world--time Montague fragments. Provides the `MontagueWorldTime` module used by `kratzer2.v`. |
| `PTQ.v` | Shallow embedding of Montague (1973) "The Proper Treatment of Quantification in Ordinary English". Hybrid: deep analysis trees + shallow IL denotations. |
| `kratzer2.v` | Shallow embedding of Kratzer's conversational backgrounds. Contains the `kratzer_equals_montague` theorem proved by `reflexivity`. |
| `PTQ_deep2.v` | Deep embedding of Montague's Intensional Logic: `ILType` as an inductive type, IL expressions as a GADT indexed by context and type, full `eval` interpretation function, temperature-puzzle countermodel. |
| `kratzer_deep2.v` | Kratzer's modal operators built as semantic functions over the denotations of deep IL expressions. Re-proves the Kratzer--Montague equivalence and S5 axioms on top of the deep IL. |
| `theorems_deep_PTQ.v` | Metatheorems about the deep IL: every-to-some, the-entails-a, relative-clause restriction, T and S4 axioms for the box, extensional collapse, beta-soundness, up/down identity, temperature non-entailment. |

## Other files

The repository also contains additional Coq formalisations from a broader research programme on type-theoretic and event semantics --- Champollion-style event semantics, Dowty's thematic proto-roles, Lakoff prototypes, file-change-style fragments, polydefinites, presupposition projection, and so on. These are not part of the paper's case study but are kept here for reference and reuse.

## Building

A `_CoqProject` and a generated `Makefile` (Coq 8.20.1) are provided. With Coq installed, build everything with:

```bash
make
```

If the `Makefile` is missing or out of date, regenerate it from `_CoqProject`:

```bash
coq_makefile -f _CoqProject -o Makefile
make
```

Or to build only the case-study files in dependency order:

```bash
coqc MontagueFragment.v
coqc PTQ.v
coqc kratzer2.v
coqc PTQ_deep2.v
coqc kratzer_deep2.v
coqc theorems_deep_PTQ.v
```

## Citation

If you use this code, please cite the accompanying paper:

> Chatzikyriakidis, Stergios. *Revisiting formal semantics using proof assistants*. In the Festschrift for Valeria de Paiva.

## License

MIT --- see `LICENSE`.

## Acknowledgements

The Coq development was written with assistance from an LLM-based coding assistant; the proof assistant acts as the independent validator. Thanks to Zhaohui Luo for discussions on MTT-semantics, and to Robin Cooper for collaboration on the deep/shallow comparison of Montague, TTR, and MTT.
