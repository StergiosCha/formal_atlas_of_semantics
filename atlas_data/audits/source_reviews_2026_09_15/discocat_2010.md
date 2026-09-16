# Coecke–Sadrzadeh–Clark 2010 — source review draft (ID 159)

Source: Coecke, B., Sadrzadeh, M. & Clark, S. (2010), *Mathematical Foundations
for a Compositional Distributional Model of Meaning*.
Consulted: `categorical/Coecke_2010_MathFoundationsCompositionalDistributional.pdf`,
34 pages, **arXiv:1003.4394v1, 23 March 2010**. Source reading covers this version.
The code also cites later 2013 work and other categorical sources; their full
claims are not adjudicated by this review. In particular, the normalization
finding below is not a claim about an independently checked journal edition.

## Covered claims and boundaries

| Source passage | Code evidence | Assessment |
| --- | --- | --- |
| §2.2, pp. 4–7: pregroup reductions, positive and negative syntax | `Red`, `Le`, `Examples.tv_red`, `Examples.neg_red`, compound adjoint lemmas | Substantial reduction calculus. `le_not_antisymmetric` explicitly shows that raw type strings with `Le` are a preorder, not the source's partially ordered pregroup; no quotient is constructed. |
| §3.1/3.3, pp. 8–14: composition, tensor, compact structure | Matrix laws, `snake_A`, `snake_B`, `F_deq` | Substantive, axiom-free soundness for the implemented equational calculus. `F_deq` respects the declared `deq`; it is not a completeness theorem or an identification of every derivation with common endpoints. |
| §3.4/3.5, pp. 14–16: `FVect × P` and word-to-sentence map | `F`, `tensor_words`, `meaning`, `meaning_deq` | A proof-relevant grammar-to-rational-matrix interpretation. Its relation to the exact product construction, and the omitted pregroup quotient, needs explicit coverage justification. |
| §4.1, pp. 17–20: transitive contraction, Examples 1/1b | `ExModel.ex1_true/false`, `ex1b_true/false` | Checked finite instances with a common four-dimensional noun space, not the source's separately chosen subject V and object W in full generality. |
| §4.2, pp. 20–24: lexical does/not, Example 2 | Negative grammatical reduction only | No negative-sentence meaning computation. A syntactic reduction is not the lexical semantic calculation. |
| §5, pp. 24–27: Definition 5.1, Examples 3–7 | `ex3_graded`; `ex5_loves_likesg`, `ex5_hates_likesg`, `ex5_loves_hates` | Positive graded vectors and **raw** inner products are checked. Normalized similarity and negative Examples 4, 6, 7 are not. |
| §6, pp. 28–29: semiring/Boolean relational variant | Rational matrix operations only | The Boolean/FRel case, part of the paper's stated contribution, is omitted. |

The public `meaning` function takes a reduction and an arbitrary word/vector
list without requiring `concat (map fst ws) = p`, where `p` is the reduction's
input type. Bounded matrix equality makes the soundness theorem meaningful,
and this does not refute that theorem, but a well-formed sentence API or an
explicit side condition is needed before claiming typed composition for all
word lists. Phantom matrix dimensions alone do not enforce that condition.

Do not inflate the gap list: the source explicitly discusses rational scalars
at p. 3 and justifies a strict presentation at p. 9. Neither choice by itself
proves restructuring is required. General higher-dimensional negation, full
Montague-style logical coverage and corpus experiments are future work at
p. 30. Later Frobenius relative-pronoun work is not a missing result of this
2010 paper. A parser and Preller's full coherence/completeness theorem need not
be independently reimplemented just to reproduce this paper's concrete examples.

## Normalization: a reproducible version-specific discrepancy

Definition 5.1 divides the inner product by both vector norms. In the local v1,
Example 3 gives orthogonal unit truth vectors `u`, `w` and
`v = (3/4)u + (1/4)w`. Example 5 calls `3/4` their degree of similarity and says
normalization is implicit. These assertions do not agree literally:

```text
u·u = 1                 v·v = 5/8
u·v = 3/4               cosine(u,v) = 3/sqrt(10)
(u·v)^2 = 9/16          cosine(u,v)^2 = 9/10
```

The code matches the raw Example 5 number, not Definition 5.1. The four closed
`SimilarityCheck` lemmas in [ReviewChecks.v](ReviewChecks.v) compute these
quantities from the **actual sentence vectors** produced by the existing
`meaning` function, including a proof that raw and normalized squares differ.
No square-root axiom is required for the squared comparison. The vector norms
are nonzero in this example; a general similarity definition must also address
zero vectors rather than silently using field division at zero.

The same issue is visible algebraically in the source's Example 7: swapping
the two coefficients gives raw overlap `3/8`, but both norms have square `5/8`,
so normalized overlap is `3/5`. This last comparison is source arithmetic, not
a claim that the missing lexical negation computation has been implemented.
An approved assessment must distinguish faithful replication of displayed raw
numbers from a checked correction implementing the stated normalized definition.

## Record reconciliation and dependency evidence

`atlas__discocat` records `faithful` and `as_is`. Its statement that every
numerical example in §§4–5 is reproduced is contradicted by both the source
inventory above and the code's own omissions header. Examples 2, 4, 6 and 7
are absent. The as-is rationale establishes successful encoding of an important
calculus, not coverage of all those claims or necessity of the representation
choices. Historical record wording is retained, with this proposed correction.

There are **98 proved statements, no admissions**, and the existing mechanical
sidecar reports all 98 closed. This review freshly recompiles the actual file
and kernel-rechecks its dependency closure through the diagnostic module;
`F_deq` and `meaning_deq` are explicitly queried again and are closed. These
facts deserve positive weight. They do not establish source fidelity on their
own; nor should the omitted examples erase the proved categorical results.

## Proposed disposition and next implementation

Keep ID 159 `review_required`. The supported bounded claim is: a rational
matrix interpretation of this reduction/equational calculus is sound and
reproduces selected positive examples. Do not turn that into an unqualified
whole-paper `as_is`, or into a claim that the original `major_restructuring`
forecast has been confirmed. No necessity argument for that forecast is given.

Next: add does/not lexical meanings and Examples 2/4/6/7; define normalized
similarity with explicit nonzero/zero handling and separate corrected numbers
from raw source replication; add the Boolean relational variant. Then justify
the exact source core, the V/W-to-common-N specialization and the relationship
between the code's calculus and the source's product/pregroup presentation.
Only then propose an outcome with reviewed supporting records and maintainer
approval. These are bounded follow-up tasks, not changes made in this review.
