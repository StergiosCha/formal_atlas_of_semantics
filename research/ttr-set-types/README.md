# Cooper's set membership rule

Cooper (2023), p. 59, (51)–(52), and Appendix A5, p. 403, give both directions of the rule for membership in a set type. The Atlas representation in this module covers finite labelled collections. The members are the field values. Distinct labels can carry the same value. [Book](https://doi.org/10.1093/oso/9780192871312.001.0001)

At revision `7623636`, the raw `wit_set` constructor accepted an arbitrary proposition together with a proof of it. Supplying `True` classified any labelled collection at any set type. The original file assessment describes that revision. [Historical assessment](https://github.com/StergiosCha/formal_atlas_of_semantics/blob/7623636429971f993bc2cbe1f5a7b4d91f8ff5f8/atlas_data/records/ttr_mtt__TTR_types.json)

The corrected `wit_set` takes a proof of unique labels and a typing proof for each value returned by lookup. Callers of `wit_set_proper` now pass the well-formedness proof before the proof for the members. The theorem `set_witness_iff` states the full condition on values in this representation. Theorem `set_member_elim` recovers the type of every stored field value. This also applies to nested sets. [Constructor](../../ttr_mtt/TTR_types.v) · [Theorems and examples](SetTypeChecks.v)

Run the regression and kernel recheck from the repository root with Rocq 8.20.1.

```sh
python3 -m unittest discover -s .github/tests -p test_ttr_set_types.py
```

Appendix A5 also defines the type of members associated with a set and treats pluralities. Those are separate constructions. The earlier assessment of function types (A4) also concerns separate constructors.
