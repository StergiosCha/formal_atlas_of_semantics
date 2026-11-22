# Three-way comparison of judgments in TTR, MTT and Montague

## Question

Given a linguistic example, which information must a translation retain for the same prediction to follow? Observations in this checkpoint are truth of an ordinary quantified sentence, identity of the objects counted, truth of an attitude report, necessity at a family of indices and identity of an event under modification. The question is meaningful for a particular construction and reading. An overall ranking of how close two theories are would conflate these observations.

## Sources and fragments

The [source dossier](CMM_SOURCES.md) supplies editions, sections and pages. The primary references for the formal statements are Cooper (2011) §6, Cooper (2023) §§1.4, 6.3, 7.2 and 8.3, Chatzikyriakidis and Luo (2020) §§3.2, 4.5, 5.3, 7.2, Montague (1973) §§1–3, and Luo and Soloviev (2017) §§2–5. The [report](README.md) connects these with both earlier and later analyses, including the jointly authored Element and Sutton (2024).

## Objects

* A noun type A, its realization into individuals I, a predicate on I, and a TTR type attached to each individual in one fixed assignment. For an ordinary universal the observable is truth.
* Eligible book witnesses, each with a physical and an informational projection. Each projection has a criterion for counting. The concrete tables use integers for equivalence classes. The source criteria can be arbitrary equivalence relations.
* A complete finite population of farmers and donkeys, with ownership and liking on pairs. The observer can count ownerships or distinct owners and can test whether a given owner likes one or all of their donkeys.
* A PTQ index comprises a world and a moment. A TTR assignment supplies witness sets. A role-indexed event carries its participants. A token in a TTR predicate type may witness both the action and its manner.
* An attitude report can take an intension as argument, or a content preserving a presentation and an agent's perspective. The finite test fixes an interpretation for each alternative.

## Maps and relations

1. Map a noun inhabitant to an individual, then compare its image with both the ordinary noun extension and the individuals whose TTR type has a witness. No witness-selection function is required for the universal.
2. For a numeral, map **eligible book witnesses** to eligible witnesses while keeping the relevant physical and informational distinctions. Forward preservation needs target sameness on mapped witnesses to imply source sameness on each facet. Reflection additionally requires a way to realize the target witnesses in the source with the relevant distinctions. An injection on record identity alone supplies neither facet condition.
3. Map an ownership pair to its owner. This changes multiplicities, and can reverse a majority. Restricting the domain to owners and keeping a witness available to the pronoun are independent choices.
4. Associate an assignment to each PTQ index. Relate truth of a sentence at that index to inhabitation of the associated type. Use the image of the index map as the family when comparing the two unrestricted necessity operators.
5. For a kiss, forget an event witness to obtain an ordered pair in a binary relation at an index. The finite test supplies a lexical witness assignment with typed participants. The reverse direction on bare truth requires existence of a witness. Recovering its manner requires information that the pair does not supply.
6. For attitudes, map structured content to a truth intension. Distinct descriptions can acquire exactly the same argument under this map. Compare this with two intensions related by implication which can remain distinct arguments.

## Proposed statements

| Statement in the file | Status | Scope |
|---|---|---|
| `noun_quantification_statement` | Proved in scratch | Under the two pointwise extension correspondences, MTT noun quantification and the TTR truth reading each agree with the Atlas extensional PTQ universal. The proof reuses `MTT_vs_DTS.universal_image`. |
| `modal_bridge_statement` | Proved in scratch | Conditional equivalence of the deep Atlas PTQ Box and TTR family-level necessity, for all closed object-language formulas satisfying the displayed index-wise correspondence. The proof reuses `Models.necessity_clause`. |
| `preservation_statement` | Stated | Preservation of a three-witness physical-and-informational reading between different carriers with suitable maps. |
| `role_diamond_statement` | Stated | Both paths that forget role information return the underlying occurrence of a dependent package. A closed instance is checked. Luo and Soloviev already give the original role relations. |
| `one_work_per_copy_statement` | Stated | If copy identity determines work identity among eligible entries, three informationally distinct witnesses already suffice for double distinctness. The crossed shelf deliberately exceeds this hypothesis. |

The three finite kiss interpretations are also checked exhaustively for the fixture’s two assignments and all its ordered participant pairs. The [main file](CMM_Comparison_spec.v) identifies finite interpretations and sources. Only the two general correspondence proofs are in the [probe](CMM_Comparison_spec_probe.v).

## Evidence

* Positive book case: three volumes of distinct works. Separations: three copies of one work, three works in a volume, and the crossed shelf with both marginals equal to three but no admissible triple. The display-pile case fixes the context and evaluates the same stock under two resolved criteria.
* The noun-type image agrees with TTR inhabitation for one individual and excludes another in the concrete noun assignment. Cooper's five-farmer population goes directly through the pinned functions for all three readings.
* An unrestricted two-index necessity test and an ideal-restricted test give different results on the same proposition. The general proof states separately the soundness condition at each index. A full PTQ model carries the logical assumptions displayed in `Models.model`. That parameter is visible in the theorem.
* The two kiss assignments meet the Atlas arity condition. The same people kiss in both, and only one assignment supplies a passionate witness. Two descriptions of a transaction provide the counterexample for attitudes.
* The library queries and the kernel recheck are recorded in the [assumptions](verification/CMM_assumptions.txt) and [kernel](verification/CMM_kernel.txt) logs. Existing `copred_dd1` and `copred_dd2` were compiled and queried separately with their lexical and ontology parameters.

## Limits

The comparison is source-based across the phenomena. The checked constructions cover the listed fragments. The proposal supplies no whole-grammar translation between TTR and MTT, no implementation of Sutton's full question stack, and no new proof of the metatheorems of Cₑ or UTT[E]. The corpus reprint of PTQ and later Montagovian treatments are identified separately. A finite reading can be mathematically available while its acceptability still needs judgement in context.

## Open questions

For a proof round, the first substantive choice is the empirical contrast in the counting case. Compare the library question with a neutral context using the **same** sentence, physical copies and works. Separately record whether a bound anthology counts as several books for the informants and the task. For belief, identify where a name-equation is available before translating the complement. For adverbs and events, select whether the observable is that an event occurred, that the very same event had a manner, or that its scope was licensed by the grammar.
