# Witness contract v0: implementation and source notes

Status: 30 mechanically checked statements about a bounded comparison
construction, not a whole-theory equivalence or an independent semantic review.
The implementation is [Witness_Contract.v](../../atlas/ttr/Witness_Contract.v).
Its source-reader route in the rebuilt site is `#/proof/atlas__witness_contract`.

## Passages rechecked

Text was extracted from these local artifacts on 2026-09-25. This is an
LLM-assisted source consultation, not a human or independent-review signature.
It neither resolves the Ranta edition discrepancy nor promotes a corpus record.

| Artifact under `papers/foundations/` | Printed pages / file pages | SHA256 |
|---|---|---|
| `Cooper_2023_FromPerceptionToCommunication.pdf` | 11–14 / 24–27; 404–406 / 417–419 | `3d4bfb3ac7de7e837317f31637af342bba36624c0ef09ef3e37b6d769f2feb7c` |
| `Chatzikyriakidis_Luo_2020_FormalSemanticsInMTT.pdf` | 15–16 / 28–29; 19–21 / 32–34 | `1466b40473900de40b3f60ef69bcf1415fa8d3b7f5f84138a8de70a7b36064d3` |
| `Ranta_1995_TypeTheoreticalGrammar.djvu` | 33–36 / 45–48; 39–40 / 51–52 | `2bdd22f4679144aad9e8e28f9dbc37cbb2ce569fb2c144c8c5c595370233954c` |

Cooper §1.3 makes types distinct from witness extensions; A8 uses the same
candidate witness for both conjuncts. A9 explicitly permits model-relative
type domains, which this implementation does **not** cover.

CL20 p. 16, especially note 26, explicitly uses both strong Sigma and weak
existential quantification. Pages 19–21 explicitly describe MTT semantics as
both model-theoretic and proof-theoretic: MTT is itself the meaning-carrying
language, rather than merely receiving a set-theoretic model. Cooper's
external assignment architecture is a different issue from that terminology.

Ranta §2.12 supplies separated subsets and §2.16 gives witness-bearing
propositions-as-types. The ambient Coq Sigma implementation remains an
encoding, not a literal identification of Ranta's subset judgments with `sigT`.

## Results and their limits

All names below are in `ttr.Witness_Contract`.

| Question | Named support | What is established |
|---|---|---|
| When can independent packages be rejoined without changing either package? | `Packages.image_exactly_aligned`, `join_split`, `split_join` | Exactly when their carrier projections are equal. This does not claim equality of packages that also store an arbitrary alignment proof. |
| Can recovery be unconditional? | `Packages.Separation.independent_inhabited`, `shared_empty`, `no_total_recovery` | A Boolean example has separate witnesses but no common witness; for that example there is no total recovery function. |
| Do strong MTT/Ranta packages retain the witness? | `Packages.strong_encodings_preserve_witness`, `Fragment.mtt_ranta_roundtrips` | Yes in the explicitly shared-carrier realization. The generic package result permits Type-valued fibres. This does not settle native noun ontology or signatures. |
| Does the displayed TTR translation match satisfaction? | `Fragment.ttr_adequacy`, `ttr_mtt_carrier_roundtrips`, `inhabitation_preserved_and_reflected` | For zero-arity ptypes and binary meet, at each fixed model, the translation preserves and reflects satisfaction and inhabitation, with carrier round trips. Evidence-term equality for the TTR maps is not claimed. |
| Is meet composition respected? | `Fragment.meet_compositional_at_witness`, `meet_package_roundtrips` | Meet realizes same-witness conjunction; its package conversion has both round trips. This does not identify meet with a product of independent existentials. |
| What is required across models? | `Fragment.preservation_extends_to_meets`, `reflection_extends_to_meets`, `transport_split_commutes_on_witnesses`, `reversible_transport_recovers_witness`, `whole_carrier_inhabitation` | Atom-level assignment compatibility extends inductively to meets. Transport commutes with splitting at carrier observations. Recovering carrier witnesses needs a left-inverse map. Reflection of target inhabitation needs surjectivity in addition to pointwise reflection. These are sufficient, explicitly stated conditions, not a minimality theorem. |
| Is atomic truth agreement enough? | `Fragment.ModelSeparation.separating_models_admissible`, `atomic_truth_agrees`, `atomic_truth_agreement_not_meet_agreement`, `identity_does_not_preserve_assignment_change` | Two admissible assignments agree on atomic inhabitation but differ on meet inhabitation. The identity map does not preserve the changed assignment. |

The separating assignments are reused from `TTR_Model.Countermodels`: in the
first, true and false predicates have different witnesses; in the second, they
share one. They are admissible for the recorded empty arities. This is a
separation of those observations and maps, not an impossibility result for
all translations between TTR and MTT.

## Verification and remaining work

Coq 8.20.1 checked all 30 statements. The mechanical sidecar records every
statement fingerprint and `Print Assumptions` result: 30/30 closed, no
admissions, no unresolved queries and no added axioms. Section hypotheses
remain explicit in universally quantified theorem statements. No choice,
functional extensionality, proof irrelevance or UIP was assumed.

The old proofs, paper links, P/F grades, source outcomes and retired edge
annotations are unchanged. A regression reconstructs the pre-addition atlas
from its original 86 records, recomputes its statistics and checks the original
full hash. Only this explicitly named 87th infrastructure record is excluded
from that historical comparison; its content and links have separate tests.

Remaining: source-grounded noun-ontology translations rather than an induced
common carrier; dependent records and contexts; changing type domains;
source-specific model/signature relations; and independent source-fidelity
review. No global comparison obligation or theory relation is marked complete.
