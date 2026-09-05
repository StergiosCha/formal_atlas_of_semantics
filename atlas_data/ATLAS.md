# Formalizability Atlas of Semantics — current state

Coq files audited: **64** · theorem statements: **1056** (proved 1043, admitted 12) · papers assessed: **230** · records disputed by the verifier: **0**

## Determination (four-point scale) over formalized sources

| Determination | Files |
|---|---|
| 1 as-is | 21 |
| 2 slight modification | 22 |
| 3 major restructuring | 16 |
| 4 cannot | 0 |
| n/a | 5 |

## Faithfulness verdicts

| Verdict | Files |
|---|---|
| faithful | 15 |
| partial | 37 |
| unfaithful | 10 |
| not_applicable | 1 |

## boundary (cognitive semantics)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/LakoffPrototypes.v | Lakoff, G. (1987). Women, Fire, and Dangerous Things: What Categories Reveal about the Mind. University of Chicago Press. Passages read (PDF page indices of the on-disk 752-page file): ch. 2 'From Wittgenstein to Rosch' (Zadeh, p. 39; Rosch ratings retraction, p. 67; summary, p. 81); ch. 4 'Idealized Cognitive Models' ('Cluster Models', 'Mother', pp. 103-104; bachelor/ICM fit, p. 98); ch. 5 'Metonymic Models' ('Working Mothers', pp. 109-111; composite prototype and representativeness structures, p. 112; 'Radial Structures', pp. 112-114); ch. 6 'Radial Categories' (p. 123); ch. 7 'Features, Stereotypes, and Defaults' ('Feature Bundles', p. 152); ch. 9 'Defenders of the Classical View' (Osherson & Smith, pp. 182-183; summary, pp. 198-199); ch. 13 'What's Wrong with Objectivist Cognition' ('ICM Clusterings', p. 260; 'Radial Structures', p. 262); ch. 17 'Cognitive Semantics' (Spatialization of Form, p. 360; 'Feature-Bundle Structures', 'Radial Category Structure', 'Graded Categories', 'Prototypes', pp. 364-367).; Lakoff, G. (1973). Hedges: A Study in Meaning Criteria and the Logic of Fuzzy Concepts. Journal of Philosophical Logic 2(4): 458-508 (revised from CLS 8, 1972; the 1987 book's bibliography and its p. 67 cite it as 'Lakoff 1972'). Sections read: 1 'Degrees of Truth' (birdiness hierarchy (1), degree-of-truth (4), pp. 459-461); 2 'Fuzzy Logic' (Zadeh definition (1) with max/min/1-x, p. 461; degree of entailment, p. 470); 3 'Hedges' (hedge list incl. 'a real', p. 472; technically/strictly speaking/loosely speaking/regular, pp. 475-477; criterion types (16) and informal hedge semantics (17), pp. 477-478); 4 'Fuzzy Logic with Hedges' (vector value \|\|F\|\|, def/prim/sec/char, hedge valuations (3), pp. 478-479). Not cited by the Coq file, which names only the 1987 book. (source gap) | 0/0 | unfaithful | 3 major restructuring | — | — |

## categorical / distributional

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| atlas/categorical/DisCoCat.v | Coecke, B., Sadrzadeh, M. & Clark, S. (2010). Mathematical foundations for a compositional distributional model of meaning. Linguistic Analysis 36.; Lambek, J. (2008). From Word to Sentence. (source gap) | 98/98 | faithful | 1 as-is | i, ii, iii, iv, v | — |

## definiteness and prominence

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/PolydefiniteSemantics.v | Chatzikyriakidis, S. & Spathas, G. (2023). A unified analysis of the semantics and pragmatics of Greek polydefinites. LENLS 20, Osaka (journal version 'Polydefinites as Markers of Prominence' under review). Header spells 'Chatzykiriakidis & Spathas (2023)'.; von Heusinger, K. & Schumacher, P. B. (2019). Prominence in discourse (Defs 1-3 of prominence). Journal of Pragmatics 154. (source gap) | 46/47 | partial | 3 major restructuring | iv | — |

## dynamic (file change semantics)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/FCS.v | Heim, Irene (1983). 'File Change Semantics and the Familiarity Theory of Definiteness'. In Bauerle, Schwarze & von Stechow (eds.), Meaning, Use, and Interpretation of Language, de Gruyter, pp. 164-189. On disk as a scan of the Portner & Partee (2002) reprint, ch. 9, pp. 223-248; pdftotext extraction is clean. All page numbers in this record are the reprint's. Sections used: 3 (file metaphor, diagram (8), p. 227-228), 4 (sequences, Sat(F) (9), Dom(F) (10), truth of a file (11), pp. 228-229), 6 (atomic rule (13) p. 232, Novelty/Familiarity Condition (15) p. 233, appropriateness as domain of definition of + p. 234, composition (16) and general rule (18) p. 235, (19)-(20) and truth criterion (21) p. 236), 7 (non-quantificational indefinites, pp. 236-240), 8 (0-place predicates (30) pp. 240-241, three-step procedure for universals pp. 241-242, donkey examples (31)-(33) pp. 243-245, universal rule (34) p. 245, negation rule (35) p. 246).; Heim, Irene (1982). The Semantics of Definite and Indefinite Noun Phrases. PhD dissertation, UMass Amherst. On disk as the Schoubye & Glick retypeset edition (README: pagination differs from the original); page numbers cited are the retypeset edition's. Chapter III 'Definiteness in File Change Semantics': 1.3 'File cards as discourse referents' (pp. 182-185), 1.4 'Files as common ground' (files as sets of world/sequence pairs F = {<w, a_N> : a_N satisfies F in w}, p. 186), 1.5 'File change potential and satisfaction conditions' (principle (A): S(F + phi) = S(F) intersect {a_N : a_N satisfies phi}, rules (i)/(i'), pp. 191-192), 3.2 'A truth criterion for utterances' (criterion (C), p. 214), 3.3 'Truth of an utterance with respect to a false file' (pp. 218-221), 5.1 Extended Novelty-Familiarity-Condition (p. 235 ff.), 5.2 'Novel definites and accommodation' (pp. 238-241). Also ch. II sec. 7 'On So-called Discourse Referents and Their Lifespans' (modals and propositional attitude verbs as operators subject to Existential Closure, pp. 170-172). (source gap) | 0/0 | unfaithful | 2 slight modification | iii, iv, v | extras/FCS2.v |

## dynamic semantics

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| atlas/dynamic/DPL.v | Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic. Linguistics and Philosophy 14(1):39-100.; Dekker, P. (2012). Dynamic Semantics. Springer. Sec. 2.1. (source gap) | 171/171 | faithful-with-corrections | 1 as-is | ii, iv, v | — |
| extras/DonkeyScope.v | Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic. Linguistics and Philosophy 14:39-100. (section 4's DPL fragment); Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases. PhD dissertation, UMass. (assignment-based dynamic binding, section 2 attempt 5) | 5/7 +2 adm | partial | n/a | iv | — |
| extras/FCS2.v | Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases. PhD dissertation, UMass Amherst.; Heim, I. (1983). File Change Semantics and the Familiarity Theory of Definiteness. In Meaning, Use, and Interpretation of Language, de Gruyter. | 2/4 +5 adm | unfaithful | 3 major restructuring | i, ii, iii, v | — |

## focus and alternatives

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/additive.v | Rooth, M. (1985). Association with Focus. PhD dissertation, UMass Amherst.; Rooth, M. (1992). A theory of focus interpretation. Natural Language Semantics 1:75-116. | 1/1 | unfaithful | n/a | iv, v | — |
| extras/additive_new.v | Rooth, M. (1985). Association with Focus. PhD dissertation, UMass Amherst.; Rooth, M. (1992). A theory of focus interpretation. Natural Language Semantics 1:75-116. | 17/18 +1 adm | partial | 3 major restructuring | iv, v | — |

## foundations (proof-of-concept scaffold spanning model-theoretic quantification and dynamic update at toy depth)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/PoC_Foundations.v | EU Synergy Grant Proposal 2025, 'Formalizing Formal Semantics: Machine-Verified Foundations for Natural Language Understanding' (anonymous; PDF title 'Synergy Grant Proposal: Formalizing Natural Language Semantics', printed from Chrome 137/Skia on 2025-08-01, 21 pp. A4, full text layer). Section 2 'Scientific Excellence', 2.1 'Groundbreaking Research Program', Phase 1: Classical Foundations (Years 1-2): heading p. 4, Coq modules MontagueGrammar and DynamicSemantics on p. 5 (pdftotext lines 111-131 and 132-147 of the whole document, exactly as cited by the file at l.11 and l.70). Also WP1 deliverables D1.2 'Formalized Montague Grammar with verified composition principles' and D1.3 'Dynamic semantics with information state monads' (pdftotext l.490-491).; Barwise, J. & Cooper, R. (1981). Generalized Quantifiers and Natural Language. Linguistics and Philosophy 4(2): 159-219 (JSTOR PDF, 62 pp. incl. cover sheet; journal page = PDF page + 157). The two quantifier properties the file proves for `every`: 'lives on' (first stated at S6 p. 170; section 4.4 'The Property Lives on', definition p. 178; Appendix C, C1, p. 209) and 'monotone increasing (mon-up)' (section 4.7 definition p. 184; `every N`-type NPs listed as mon-up p. 185). Secondary: the file cites only the proposal. (source gap) | 3/3 | faithful | 2 slight modification | ii | — |

## generalized quantifiers

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/Quantifiers.v | Barwise, J. & Cooper, R. (1981). Generalized quantifiers and natural language. Linguistics and Philosophy 4:159-219.; Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. Wiley/ISTE. | 9/11 +2 adm | unfaithful | 3 major restructuring | ii, iv | — |

## infrastructure

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/Set_theoretic_Defs.v | None. Helper definitions only: textbook naive set theory (membership, intersection, union, subset, proper subset, empty set) encoded as Prop-valued predicates. The file header (lines 2-3) claims nothing beyond 'Provides the basic set operations used in Champollion.v'.; Downstream only, not a source for this file: Champollion, L. (2010) Parts of a Whole (dissertation) / (2017) Parts of a Whole (OUP). This is the source of the two consumers Champollion.v and champollion_full.v, which refer to it e.g. as 'Champollion 45'. (source gap) | 0/0 | not_applicable | n/a | ii | — |

## inquisitive semantics

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| atlas/inquisitive/InqB.v | Ciardelli, I., Groenendijk, J. & Roelofsen, F. (2018). Inquisitive Semantics. OUP. Chs. 2-4.; Roelofsen, F. (2013). Algebraic foundations for the semantic treatment of inquisitive content. Synthese 190:79-102. | 192/192 | faithful | 1 as-is | i, ii, iii, iv, v | — |

## model-theoretic

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/theorems_PTQ.v | Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English. Reprint pagination on disk (pp. 17-34): analysis trees and their equivalence p. 22; IL semantics clauses 1-10 pp. 24-25; type map f and T1 p. 25-26; T2-T4 p. 26; T14 p. 27; meaning postulates (1)-(9) and 'logically possible interpretation' p. 28; starred reduction and derived formulas box[delta(x) <-> delta*(v x)] with editors' note p. 29; Section 4 examples pp. 29-31 including the Partee argument pp. 30-31; Thomason notes 9, 10, 12.; Dowty, D., Wall, R. & Peters, S. (1981). Introduction to Montague Semantics. Ch. 5 p. 128 (5-20) box-phi -> phi valid; p. 132 'necessarily always' chosen 'because Montague also used this interpretation'; p. 139 Exercise 3(ii) box-phi -> box-box-phi valid; Appendix III pp. 279-281 (7-120)-(7-122'), f(IV)=f(CN)=<<s,e>,t>, MP6. (source gap) | 12/12 | partial | 2 slight modification | ii, iv, v | deep/theorems_deep_PTQ.v |

## model-theoretic (aspect)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/Aspect.v | Dowty, D. R. (1979). Word Meaning and Montague Grammar. Reidel. Relevant sections per the on-disk TOC: ch. 3 'Interval Semantics and the Progressive Tense' (§3.1 The Imperfective Paradox p. 133; §3.2 Truth Conditions Relative to Intervals, not Moments p. 138; §3.4 Truth Conditions for the Progressive p. 145; §3.6 On the Notion of 'Likeness' Among Possible Worlds); ch. 7 'The Syntax and Semantics of Tenses and Time Adverbials in English' (§7.4 The Syntactic Structure of the Auxiliary p. 336; §7.5 The Present Perfect p. 339; §7.7 An English Fragment p. 350); ch. 2 §2.3.6 Accomplishments and CAUSE p. 91. Foreword p. vii states ch. 3's innovation is truth relative to an interval rather than a moment. ONLY the 23-page front matter is on disk.; Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English. §2 Intensional Logic: syntax clause 5 (Wφ, Hφ ∈ ME_t), interpretation ⟨A, I, J, ≤, F⟩ with J the moments of time and ≤ a simple (linear) ordering; semantic clause 8: [Wφ]^{A,i,j,g}=1 iff φ^{A,i,j',g}=1 for some j' with j ≤ j', j' ≠ j; [Hφ]^{A,i,j,g}=1 iff φ^{A,i,j',g}=1 for some j' with j' ≤ j, j' ≠ j. §3 S17 (F11-F15: negation, future, negative future, present perfect, negative present perfect). §4 T17: F14(α,δ) translates into Hα'(^δ') (present perfect = past operator H over the term-plus-IV formula). (source gap) | 1/1 | unfaithful | 3 major restructuring | ii, iii, iv | extras/Imperfective2.v |

## model-theoretic (aspect, imperfective paradox)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/Imperfective2.v | Dowty, D. R. 1979. Word Meaning and Montague Grammar. Reidel. Ch. 3 'Interval Semantics and the Progressive Tense': 3.1 The Imperfective Paradox (p. 133), 3.2 Truth Conditions Relative to Intervals, not Moments (p. 138), 3.4 Truth Conditions for the Progressive (p. 145), 3.6 On the Notion of 'Likeness' Among Possible Worlds (p. 150); also 7.5 The Present Perfect (p. 339).; Dowty, D. R. 1977. 'Toward a semantic analysis of verb aspect and the English "imperfective" progressive', Linguistics and Philosophy 1: 45-78 (the original version of ch. 3; cited as ref. 36 in DWP 1981). (source gap) | 7/7 | partial | 2 slight modification | iv, iii | extras/ImperfectiveParadox.v |

## model-theoretic (deep)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| deep/theorems_deep_PTQ.v | Montague, R. (1973). 'The Proper Treatment of Quantification in Ordinary English'. Reprint on disk (pp. 17-34 pagination): sec. 2 IL syntax/semantics pp. 23-25 (clauses 1-10, clause 8 for box/W/H, clauses 9-10 for ^ and v); sec. 3 type map f(A/B)=<<s,f(B)>,f(A)> p. 25, T1-T17 pp. 26-27, meaning postulates (1)-(9) p. 28, starred reductions p. 29; sec. 4 examples pp. 29-31 incl. the Partee temperature argument pp. 30-31; Thomason editorial notes 9 ('necessarily always'), 10 (corrected clauses 1/9 and the [v^alpha] corollary), 12 (T3 variable collision), pp. 33-34.; Dowty, D., Wall, R. & Peters, S. (1981). Introduction to Montague Semantics. Ch. 5 p. 132 ('necessarily always' vs 'necessarily now', Montague used the former in PTQ); Ch. 5 p. 131 (system S5 'is essentially the one used by Montague in PTQ'); Ch. 5 Exercise 3 p. 139 (validity of box phi -> box box phi, schema (ii)); Ch. 6 (6-17) p. 154 ('down-up cancellation', with the remark that the converse fails); Ch. 7 (7-8) T4 p. 192 and derivation (7-18) p. 196 ('every man talks' via T2, T4, lambda-conversion, down-up); Appendix III pp. 279-282 (temperature puzzle (7-120)-(7-122'), f(IV)=f(CN)=<<s,e>,t> p. 280, MP6/MP7 p. 281). (source gap) | 10/10 | partial | 2 slight modification | ii, iv | extras/theorems_PTQ.v |

## model-theoretic (focus/alternatives)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/FocusEven.v | Rooth, M. (1992). A Theory of Focus Interpretation. Natural Language Semantics 1:75-116 (author preprint, 41 pp.; page numbers below are preprint pages).; Rooth, M. (1985). Association with Focus. PhD dissertation, UMass Amherst (image-only scan, 237 PDF pages; dissertation page N = PDF page N+10). (source gap) | 3/3 | partial | 2 slight modification | iii, iv | extras/FocusEven2.v |
| extras/FocusEven2.v | Rooth, Mats (1992). A Theory of Focus Interpretation. Natural Language Semantics 1: 75-116. Author preprint, 41 pp., full text layer. Used: sec.1 (2) focus semantic values and p.2 'the ordinary semantic value is always an element of the focus semantic value'; sec.2.1 (3)-(9): only as quantification over properties with domain C, fn.2 (P(m) as presupposition or assertion), fn.3 ('=' is identity in intension), (9c) C subset of [[VP]]f; sec.2.3 (16)-(22): scales as posets ordered by entailment, (22) constraint on scales; sec.3 (26a-d), (27) Focus Interpretation Principle, (30)-(31) only(C); sec.4 (32), (36)-(39), (40) presuppositions of the ~ operator, (42) closure clause.; Rooth, Mats (1985). Association with Focus. PhD dissertation, UMass Amherst. Complete 237-page scan, image-only (pdftotext returns whitespace); dissertation page N = PDF page N+10. Read as page images: front matter pp.i-x; Ch.II sec.3 'Domain Selection Theory' (21)-(35) pp.41-45 (only'' with free domain variable C, the introduce-Bill/Sue example); 'Formalization' pp.45-59: (36) denotation spaces, (38) p-set intension/extension problem, (39) constant meanings, (40) ILF formation rules, (41a)-(41l) meaning assignment with p-sets, (42) restriction operator R, (43) translation rule for only; Ch.III sec.3 pp.120-124: (61) F_only/F_even, (62) crosscategorial family, (63)-(64) 'John_F even came', (65)-(66) 'John only likes Mary_F', (67)-(70) 'even John_F came'; Ch.IV sec.1 pp.139-143: KKP existential/scalar implicatures (3a,b), meaning postulate (4), scope ambiguity (5)-(7). (source gap) | 3/3 | partial | 2 slight modification | iv | extras/FocusEven.v |

## model-theoretic (generalized quantifiers)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/BarwiseCooper.v | Barwise, J. & Cooper, R. (1981). Generalized Quantifiers and Natural Language. Linguistics and Philosophy 4(2): 159-219. (source gap) | 6/6 | partial | 1 as-is | iv | — |

## model-theoretic (modality)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/shallow/kratzer2.v | Kratzer, A. (1977). What 'must' and 'can' must and can mean. Linguistics and Philosophy 1(3): 337-355. Defs 1-4 p. 344; Def. 5 p. 346; Def. 6 p. 347; sec. 2.1-2.2 New Zealand judgements pp. 347-352; Def. 7 p. 351; Def. 8 p. 352; sec. 2.3 Whare Wananga (Te Miti / Te Kini) pp. 352-354.; Kratzer, A. (2012). Modals and Conditionals. OUP. Ch.1 = revised 1977 (Defs 1-4 p. 12 with fn. 6 'must and can are duals ... the definitions do not assume compactness for premise sets'; Def. 7 p. 15 as n(p,f) = {w : for all A in X_f(w) exists B in X_f(w), A subset B and intersection B subset p}; Def. 8 p. 16; sec. 1.4 pp. 17-19 on {p, q} versus {p intersection q}). Ch.2 = revised 1981 'The Notional Category of Modality' (sec. 2.3 'Basic notions' p. 31 simple f-necessity/f-possibility, pp. 32-33 realistic / totally realistic / empty backgrounds with accessible worlds = intersection f(w); sec. 2.4 pp. 39-40 the induced preorder <=_A, necessity and possibility w.r.t. f and g). Ch.3 = 1991 'Modality' (not used by the file). (source gap) | 10/10 | partial | 1 as-is | iv, v, iii | /Users/graogro/Dropbox/revisiting-formal-semantics/extras/kratzer_1977.v |
| extras/kratzer_1977.v | Kratzer, A. (1977). What 'must' and 'can' must and can mean. Linguistics and Philosophy 1: 337-355.; Kratzer, A. (2012). Modals and Conditionals. OUP. Chapter 1 (revised reprint of Kratzer 1977), incl. 'Introducing Chapter 1'. (source gap) | 6/6 | partial | 1 as-is | iv, v | shallow/kratzer2.v |

## model-theoretic (modality, deep)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/deep/kratzer_deep2.v | Kratzer, A. (1977). What 'must' and 'can' must and can mean. Linguistics and Philosophy 1(3): 337-355.; Kratzer, A. (2012). Modals and Conditionals. OUP. Ch.1 (rev. of 1977), Ch.2 'The Notional Category of Modality' (rev. of 1981), Ch.3. (source gap) | 13/13 | partial | 2 slight modification | iv, v | shallow/kratzer2.v |
| extras/kratzer_deep.v | Kratzer, A. (2012). Modals and Conditionals: New and Revised Perspectives. OUP. Ch.1 'What Must and Can Must and Can Mean' (revised Kratzer 1977), secs 1.1-1.4, pp.4-20; ch.2 'The Notional Category of Modality' (revised 1981), sec.2.3 'Basic notions' p.31.; Kratzer, A. (1977). What 'must' and 'can' must and can mean. Linguistics and Philosophy 1(3): 337-355. Definitions 1-4 p.344, Definition 5 p.346, Definition 6 p.347, sec.2.1 pp.347-349, Definitions 7-8 pp.351-352. (source gap) | 6/6 | partial | 1 as-is | iv, v | deep/kratzer_deep2.v |

## model-theoretic (plurals/coordination: Boolean set-based semantics with choice functions; the region hint 'mereology/events' does not fit this file, which has no part structure and no events)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/champollion_full.v | Champollion, L. (2016) 'Ten men and women got married today: noun coordination and the intersective theory of conjunction', Journal of Semantics 33(3): 561-622, doi:10.1093/jos/ffv008. The actual source of every construct in the file. NOT under papers/; the only on-disk copy, /Users/graogro/Dropbox/formal_semantics_coq/2016-noun-coordination.pdf, is a 0-byte placeholder ('file' reports 'empty'; pdftotext: 'Document stream is empty'). For this audit the author's final pre-publication version (lingbuzz/002025, 'Final pre-publication version, June 2015', 46 pp.) was fetched and text-extracted; example numbers below are the preprint's. Relevant loci: sec.2.2 (12) Existential Raising, (13), (14)-(16) INT and the intersective theory of and, (17) generalized conjunction, (18) ER(man) and ER(woman), (19a/b) Minimization, (20) MIN(ER(man) and ER(woman)) = mw-pair (10); sec.2.3 (21) 'A man and woman who dated met in the park', (22a) [[dated]] = lambda P_et. date(P), (22b) met, (23) [[a]], (24) hydra derivation, (25) 'A man and woman had a beer', (27) PDIST, (28a-b) have a beer, (29a-f) derivation; sec.3.1 (35) LIFT; sec.4.2 (45) [[some_i]]^g with definedness condition and 'where g(i) is a choice function', (46) Choice Raising CR_i, (47) Predicate Abstraction, (48)-(50) Choice Closure and the CF gloss, (51)-(55) John and some man; sec.4.3 (41) 'A doctor and lawyer met', (56) LF, (57a-h) derivation, (58); sec.5.2-5.3 (71)-(72) plurals via PDIST, (74)-(76) mixtures, (78)-(80) DCR.; Champollion, L. (2017) Parts of a Whole: Distributivity as a Bridge between Aspect and Measurement, OUP (corrected proof, 331 pp.). Nominated as primary source but is not the source of anything in this file. Verified by grep of the full text layer: 'choice function' occurs only in the bibliography entry for Winter 1997; no PDIST, INT, CR, Choice Closure, 'man and woman', 'have a beer'; 'MIN' occurs only as min(V), a truthmaker-style minimal-event operator in the stratified-reference discussion around (46)-(47) of the aspect chapter (text-layer lines 9386-9391), unrelated to Winter's set minimization. The single contact point is one sentence in Ch. 8 'Overt distributivity' beside (101) (text-layer lines 11722-11727): the author remains 'noncommittal' between a sum-based and and 'an intersective denotation that involves Montague-lifting the two event predicates and then minimizing their intersection, as in Winter (2001) and Champollion (2015d, 2016d)'. (source gap) | 1/1 | partial | 2 slight modification | ii, iii, iv | extras/Champollion.v |

## model-theoretic (plurals/mereology)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/Link1983.v | Link, G. (1983). The Logical Analysis of Plurals and Mass Terms: A Lattice-theoretical Approach. In R. Bäuerle, C. Schwarze & A. von Stechow (eds.), Meaning, Use, and Interpretation of Language, de Gruyter, 302-323. The copy on disk is the reprint as ch. 4 of P. Portner & B. Partee (eds.) 2002, Formal Semantics: The Essential Readings, Blackwell, pp. 127-146 (20 scanned pages); all page numbers below refer to the reprint. Relevant parts: Sec. 1 pp. 130-134 (star operator, atoms, (15) Π-biconditional, (16), (17) σ/σ*, (18) μ, (19)-(22) material part and h, (23)-(26) ᵐP, (27) Distr, (28)-(32) distributive inference and ᵀ, (33)-(46) formalisations); Sec. 2 pp. 135-139 (LPM: (D.1)-(D.21), (MP.1)-(MP.2), boosk (D.22), (D.23)-(D.24) ≤m/∼m, model (D.25), truth conditions (D.26)-(D.32), (47)-(64), theorems (T.1)-(T.32)); Sec. 3 pp. 140-144 (TITL', (65)-(76)). (source gap) | 5/5 | partial | 2 slight modification | iii, iv | — |

## model-theoretic (shallow substrate: extensional / world-indexed / world-time-indexed fragments with generalized-quantifier NPs and an axiomatized counting interface)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/Montague.v | Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English (reprint pp. 17-34; line numbers are of `pdftotext montague73.pdf -`). §1 lexicon: B_T = {John, Mary, Bill, ninety, he_n} (92), B_TV = {find, lose, eat, love, date, be, seek, conceive} (93), B_CN = {man, woman, park, fish, pen, unicorn, price, temperature} (95); S2/F0-F2: every / the / a-an are the only determiners (113-116). §2: Type = smallest set with e, t, <a,b>, <s,a> (350-352); A, I, J = entities, possible worlds, moments of time (398-399); D_e = A, D_t = {0,1}, D_<a,b> = D_b^{D_a}, D_<s,a> = D_a^{I x J} (406-409); interpretation <A,I,J,<=,F> with A,I,J nonempty and <= a linear ordering of J (413-416); extension at point of reference <i,j> (420-423); clause 7 quantifier semantics (448-450); clause 8: [box phi]^{A,i,j,g} = 1 iff phi = 1 for all i' in I and all j' in J, plus W/H tense clauses (452-460); Thomason note 9: box is 'necessarily always' (896). §3: f(A/B) = f(A//B) = <<s,f(B)>,f(A)> (503-506); T1(d) John -> j* = lambda P. P{^j} (535); T2 every/the/a (537-538); T4, T5 delta'(^beta') (551-554); meaning postulates (1)-(9) (630-642), in particular (5) subject-extensionality of seek (637) and (9) seek' = try-to'(^find') (641-642), discussed 660-666; d* reduction (687-696). §4 examples: every man walks = forall u[man'*(u) -> walk'*(u)] (719); John finds a unicorn (723); John seeks a unicorn de dicto seek'(^j, ^lambda P exists u[unicorn'*(u) and P{^u}]) vs de re exists u[unicorn'*(u) and seek'*(j,u)] (733-738).; Dowty, Wall & Peters (1981). Introduction to Montague Semantics (image-only PDF; line numbers are of the DjVu-OCR .txt sidecar). Ch. 3 p. 61 (txt 2934-2945): 'most', 'few', 'many' 'have no ready correspondents in predicate logic'; the book's fragment 'will consider only the quantifiers every, some, and the'. Ch. 5 p. 127 (txt 5250-5252): box phi is true iff phi is true 'with respect to all possible worlds, not just those standing in a certain relation to the actual one' - no accessibility relation; p. 129 (txt 5419-5421): the system is S5, 'essentially the one used by Montague in PTQ'; pp. 131-132 (txt 5465-5478): index <w,t>; two candidate readings of box, 'necessarily always' (all <w',t'>) vs 'necessarily now' (all <w',t>, t fixed); the book chooses the former 'because Montague also used this interpretation of the necessity operator in PTQ'. Ch. 6 (6-10) 'John is seeking a unicorn' (txt 5905). Ch. 7 pp. 185-186 (txt 7657-7672): every A/B functor applies to the intension of its B argument; seek and find 'are both interpreted as functions applying to the intensions of term phrases'. Ch. 7 pp. 215-217 (txt 8926-8953): S5/T5 and derivation (7-60)/(7-61) of the de dicto reading seek'(j, ^lambda Q exists x[unicorn'(x) and Q{x}]). (source gap) | 0/0 | partial | 1 as-is | iv, iii, v | shallow/MontagueFragment.v |
| /Users/graogro/Dropbox/revisiting-formal-semantics/shallow/MontagueFragment.v | Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English (reprint, pp. 17-34; pdftotext line numbers of montague73.pdf). §1 lexicon: B_T = {John, Mary, Bill, ninety, he_n} (line 92), B_TV = {find, lose, eat, love, date, be, seek, conceive} (93), B_CN = {man, woman, park, fish, pen, unicorn, price, temperature} (95); S2/F0-F2: every / the / a-an are the only determiners (113-116). §2: Type := smallest set with e, t, <a,b>, <s,a> (350-352); A, I, J = entities, possible worlds, moments of time (398-399); D_<s,a> = D_a^{I x J} (409); interpretation <A,I,J,<=,F> with A,I,J nonempty and <= a linear ordering of J (413-416); extension at point of reference <i,j> (421-423); clause 8: [box phi] = 1 iff phi = 1 for all i' in I and all j' in J, plus W/H tense clauses (452-472); Thomason note 9: box is 'necessarily always' (896). §3: f(A/B) = <<s,f(B)>,f(A)> (506); T1(d) John -> j* = lambda P. P{^j} (535); T2 every/the/a (537-538); T4, T5 delta'(^beta') (551-554); meaning postulates (1)-(9) (630-642), in particular (5) subject-extensionality of seek (637) and (9) seek' = try-to'(^find') (641-642, 665-666); d* reduction (687-696). §4 examples: every man walks = forall u[man'*(u) -> walk'*(u)] (719); John finds a unicorn (723); John seeks a unicorn de dicto seek'(^j, ^lambda P exists u[unicorn'*(u) and P{^u}]) vs de re exists u[unicorn'*(u) and seek'*(j,u)] (733-738).; Dowty, Wall & Peters (1981). Introduction to Montague Semantics (DjVu-OCR text layer; line numbers of the .txt). Ch. 5 pp. 126-127 (txt 5234-5262): Kripke models as indexed families; box phi true iff phi true 'with respect to all possible worlds, not just those standing in a certain relation to the actual one' - i.e. no accessibility relation; Sem B.10. Ch. 5 pp. 131-132 (txt 5465-5478): index <w,t>; two candidate readings of box, 'necessarily always' (all <w',t'>) vs 'necessarily now' (all <w',t>, t fixed); the book chooses the former 'because Montague also used this interpretation of the necessity operator in PTQ'. Ch. 7 pp. 185-186 (txt 7615-7670): seek is TV = IV/T and, like every A/B functor, 'denotes functions applying to the intensions of expressions of category B' - the intension of a term phrase. Ch. 7 pp. 215-217 (txt 8936-8947, 9093-9122): derivations (7-60)/(7-61) of the de dicto and de re readings of John seeks a unicorn. Determiner 'most' appears only as illustrative sentence (1-1) 'Most dentists won't make house calls' (txt 646) and receives no semantics; 'at least two unicorns' appears once, as an exercise (txt 10232). (source gap) | 0/0 | partial | 1 as-is | iv, iii, v | extras/Montague.v |

## model-theoretic (tense)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/DowtyTense.v | Dowty, D. R. (1979). Word Meaning and Montague Grammar. Reidel. Relevant: ch. 3 'Interval Semantics and the Progressive Tense' (esp. 3.2 'Truth Conditions Relative to Intervals, not Moments', p. 138) and ch. 7 'The Syntax and Semantics of Tenses and Time Adverbials in English: An English Fragment' (pp. 322-350+, esp. 7.1 syncategorematic tense/adverbial interaction, 7.5 present perfect, 7.7.1 'Basic Model-Theoretic Definitions' p. 339).; Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English (PTQ). Relevant: sec. 8 interpretation <A,I,J,<=,F> with <= a simple (linear) ordering of moments J, D_<s,a> = D_a^(I x J) (p. 24 of the Thomason reprint); semantic clause 9 for W ('for some j' with j <= j', j != j'') and H ('for some j' with j' <= j, j' != j') (p. 25); syntactic rule S17 / F12-F15 and translation rule T17 (future W, present perfect H). (source gap) | 1/1 | partial | 1 as-is | iv | — |

## model-theoretic (thematic proto-roles); neo-Davidsonian event layer over shallow/MontagueFragment.v MontagueExtensional

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/dowty_roles.v | Dowty, David (1991). Thematic Proto-Roles and Argument Selection. Language 67(3): 547-619. Relevant: §7 lists (27) p.572 and (28) p.572 with fn.16; §8.1 (31) ASP, (32) Corollary 1, (33) Corollary 2, (34) Nondiscreteness, p.576; p.574 remarks on movement and weighting; §8.2 hierarchies (36)-(37) p.578. (source gap) | 1/1 | unfaithful | 2 slight modification | iii, v | — |

## model-theoretic/dynamic (presupposition)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/PresuppositionProjection.v | Heim, I. (1983). On the Projection Problem for Presuppositions. WCCFL 2, 114-125; on disk as the Portner & Partee (eds.) 2002 reprint, Formal Semantics: The Essential Readings, ch. 10, pp. 249-260 (page numbers in this record refer to the reprint). Section 1.1 (K&P content/presupposition/heritage properties; rule (4): presupposition of 'If A, B' is p' & (p -> q'), p. 250); 1.2 (examples (5)-(6), disjunction and 'stopped smoking' counterexamples, p. 251); 1.3 (quantified sentences (7)-(9), free-variable presuppositions, pp. 251-252); 2.1 ((10) local contexts, (11) admittance, (12) 'S presupposes p iff all contexts that admit S entail p', p. 252); 2.2 ((13) truth via CCP, (14) c + If A,B = c \ (c+A \ c+A+B), (15) c + Not S = c \ c+S, negation as a Karttunen-1973 'hole', pp. 253-254); 2.3 (global vs local accommodation, example (16) 'The king of France didn't come', pp. 254-255); 3.1 ((17)-(20) contexts as sets of sequence-world pairs, pp. 255-256); 3.2 ((21) CCP of 'every', (22) novelty condition, 'Every x, A, B' presupposes 'Every x, A, X', (23)-(24), pp. 256-258); 3.3 ((25)-(27) indefinites, p. 258); 4 (explicitly defers 'or', modals and propositional attitude verbs, p. 259).; Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases. Ph.D. dissertation, UMass Amherst; on disk as the Schoubye & Glick retypeset edition (pagination differs from the original). Relevant parts: Ch. II 6.2 'The felicity conditions of definites with descriptive content' (definites presuppose their descriptive content (4b) cat(x1), not existence-and-uniqueness (4c); uniqueness argued to follow from felicity conditions, pp. 153-157); Ch. II 6.3 'Non-referring definites and a projection problem for felicity conditions' (K&P quantifiers as filters; universal rule (8); existential rule (12); 'and' rule (13): [phi /\ psi] presupposes [chi /\ [phi -> xi]]; the existential-projection problem, pp. 157-163); Ch. III 2.5 'The Novelty-Familiarity-Condition and the Projection Problem' (a complex formula is felicitous w.r.t. F iff every elementary step in computing F + phi respects the felicity conditions, pp. 208-211); Ch. III 5.2 'Novel definites and accommodation' (accommodation as file adjustment with bridging cross-references, pp. 238-241). (source gap) | 8/8 | unfaithful | 2 slight modification | ii, iv | — |

## modern type theories (MTT + Ranta pair)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| atlas/mtt_ranta/DTS.v | Bekki, D. (2014). Representing anaphora with dependent types. LACL, LNCS 8535.; Bekki, D. & Mineshima, K. (2017). Context-passing and underspecification in Dependent Type Semantics. In Chatzikyriakidis & Luo (eds), Modern Perspectives in Type-Theoretical Semantics. | 7/7 | partial | 2 slight modification | i, ii, iv | — |
| atlas/mtt_ranta/MTT.v | Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. ISTE/Wiley.; Luo, Z. (2012). Common nouns as types. LACL. | 33/33 | faithful | 1 as-is | i, ii, iii, iv | — |
| atlas/mtt_ranta/MTT_vs_Ranta.v | Chatzikyriakidis & Luo 2020, §1.4.2, §2.3.1, §3.2-3.3.; Ranta 1995, §2.12, §2.16, §3.1, §3.7, §4.2, ch. 9. | 15/15 | faithful | 1 as-is | i, iv | — |
| atlas/mtt_ranta/Ranta.v | Ranta, A. (1995). Type-Theoretical Grammar. OUP. | 14/14 | faithful | 1 as-is | i, ii, iii, iv | — |

## montague lineage

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| atlas/montague/PTQ.v | Montague, R. (1973). The proper treatment of quantification in ordinary English.; Dowty, Wall & Peters (1981). Introduction to Montague Semantics, ch. 7. | 19/19 | faithful | 1 as-is | i, ii, iv | — |
| atlas/montague/PTQ_vs_Lambek.v | Montague 1973 (via atlas/montague/PTQ.v); Moot & Retore 2012 ch. 3, Lambek 1958 (via atlas/type_logical/Lambek.v). | 4/4 | faithful | 1 as-is | iv | — |
| atlas/montague/PTQ_vs_MTT.v | Montague 1973 (via atlas/montague/PTQ.v); Chatzikyriakidis & Luo 2020 §3.2-3.3 (via atlas/mtt_ranta/MTT.v); Luo 2012. | 4/4 | faithful | 1 as-is | iv | — |

## montague lineage (raw material)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| deep/PTQ_deep2.v | Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English. In Hintikka, Moravcsik & Suppes (eds.), Approaches to Natural Language, 221-242.; Dowty, D., Wall, R. & Peters, S. (1981). Introduction to Montague Semantics. Reidel. [secondary source used to verify the f(IV) type map (7-2), Appendix III, and the PTQ necessity clause pp. 132-133] | 13/13 | partial | 3 major restructuring | iv, ii | — |
| shallow/PTQ.v | Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English. In Hintikka, Moravcsik & Suppes (eds.), Approaches to Natural Language, 221-242. Reidel. (File cites pp. 19, 25, 28, 29-32.); Dowty, D., Wall, R. & Peters, S. (1981). Introduction to Montague Semantics. Reidel. (Secondary exposition of PTQ.) | 8/9 +1 adm | partial | 2 slight modification | iv, ii, iii | — |

## plurality and coordination

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/Champollion.v | Champollion, L. (2016). Ten men and women got married today: Noun coordination and the intersective theory of conjunction. Journal of Semantics 33(3):561-622.; Winter, Y. (2001). Flexibility Principles in Boolean Semantics. MIT Press. (origin of the ER/MIN/choice-closure operator inventory that Champollion 2016 adopts) | 0/0 | partial | 3 major restructuring | iv, ii | — |

## probabilistic pragmatics

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| atlas/probabilistic/RSA.v | Goodman, N. & Frank, M. (2016). Pragmatic language interpretation as probabilistic inference. TiCS 20:818-829.; Frank, M. & Goodman, N. (2012). Predicting pragmatic reasoning in language games. Science 336:998 (+ Supplement). (source gap) | 117/117 | faithful | 1 as-is | ii, iii, iv, v | — |

## tense and aspect

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/ImperfectiveParadox.v | Dowty, D. (1979). Word Meaning and Montague Grammar, ch. 3 (the imperfective paradox and the inertia-worlds progressive). Reidel.; Dowty, D. (1977). Toward a semantic analysis of verb aspect and the English 'imperfective' progressive. Linguistics and Philosophy 1:45-77. (source gap) | 6/7 +1 adm | partial | 3 major restructuring | iv | — |

## ttr pilots

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| ttr_mtt/Book_Event_Adv.v | Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. Wiley/ISTE. §4.5.2 (manner, agent-oriented and speech-act adverbs, eqs. 4.56-4.65), §6.3.1 (example 6.2), Appendix A7.8 (Manner adverbs).; Luo, Z. & Soloviev, S. (2017). Dependent event types (cited by the book as the origin of EvtA/EvtM/EvtAM; discussed in book §7.2). (source gap) | 1/1 | partial | 2 slight modification | iv | — |
| ttr_mtt/Book_Homonymy.v | Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. Wiley/ISTE. §3.3.2 (homonymy and overloading, eqs. 3.34-3.40, Figure 3.1) and Appendix A7.2 (the Coq code this file transcribes).; Luo, Z. (2011b). Contextual analysis of word meanings in type-theoretical semantics. LACL 2011, LNAI 6736. (Original proposal of the overloading treatment; content reproduced in the 2020 book.) | 0/0 | partial | 1 as-is | iv, ii | — |
| ttr_mtt/Book_Individuation.v | Chatzikyriakidis, S. & Luo, Z. (2018). Identity criteria of common nouns and dot-types for copredication. Oslo Studies in Language 10(2):121-141.; Luo, Z. (2012). Common nouns as types. LACL 2012, LNCS 7351:173-185. | 20/20 | faithful | 2 slight modification | ii, iv | — |
| ttr_mtt/Book_Inter_Sub.v | Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. ISTE/Wiley. Ch. 6 (Reasoning and Verifying NL Semantics in Coq), sec. 3.3, and Appendix A7.3 (pp. 194-195) — the file is a near-verbatim transcription of A7.3.; Chatzikyriakidis, S. & Luo, Z. (2013). Adjectives in a Modern Type-Theoretical Setting. LACL 2013 — the underlying analysis of subsective adjectives as polymorphic predicates. | 3/4 | faithful | 2 slight modification | ii, iv | — |
| ttr_mtt/Book_Multi.v | Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. ISTE/Wiley. §4.4 (Multidimensional adjectives) and Appendix A7.5.; Sassoon, G. (2012/2013). A typology of multidimensional adjectives. Journal of Semantics 30(3):335-380 (the positive/negative universal-vs-existential typology the book follows). (source gap) | 3/5 | faithful | 1 as-is | iv | — |
| ttr_mtt/Book_gradable.v | Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. Wiley/ISTE. Ch. 4 'Advanced Modification', §4.2 (eqs. 4.17-4.27) and §4.3 (eqs. 4.31-4.36).; Chatzikyriakidis, S. & Luo, Z. (2013). Adjectives in a modern type-theoretical setting. (antecedent account the book's §4.2 builds on, with C&L 2014/2017a) (source gap) | 5/5 | partial | 3 major restructuring | ii, iv | — |
| ttr_mtt/Book_veridical.v | Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. Wiley/ISTE. §4.5.1 (defs 4.50-4.53, claims 4.51-4.52), §6.3.1, Appendix A7.7.; Chatzikyriakidis, S. & Luo, Z. (2014). Natural Language Inference in Coq. J. of Logic, Language and Information 23 (background: veridical adverbs for FraCaS). (source gap) | 3/3 | partial | 1 as-is | iv | — |
| ttr_mtt/Coq_book_ontology.v | Chatzikyriakidis, S. & Luo, Z. (2014). Natural Language Inference in Coq. Journal of Logic, Language and Information 23(4):441-480.; Luo, Z. (2012). Common Nouns as Types. LACL 2012, LNCS 7351. | 0/0 | partial | n/a | ii, iv | — |
| ttr_mtt/TTR_base.v | Cooper, R. (2023). From Perception to Communication: A Theory of Types for Action and Meaning. Oxford University Press. Appendix A1 (underlying set theory), A11 (record types). | 4/4 | partial | 3 major restructuring | i, ii, iv | — |
| ttr_mtt/TTR_records.v | Cooper, R. (2023). From Perception to Communication: A Theory of Types for Action and Meaning. Oxford University Press. Appendix A11 (records and record types). | 2/2 | partial | 3 major restructuring | ii, iv, v | — |
| ttr_mtt/TTR_shallow.v | Cooper, R. (2023). From Perception to Communication: An Enriched Approach to the Semantics and Pragmatics of Dialogue. Oxford University Press. (Appendix A: A1, A4, A6, A9, A10, A11; p. 397 quoted in header.); Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. Wiley/ISTE. (Secondary source for the MTT comparison half.) | 1/1 | partial | 3 major restructuring | ii, iv | — |
| ttr_mtt/TTR_theorems_deep.v | Cooper, R. (2023). From Perception to Communication: A Theory of Types for Action and Meaning. Oxford University Press. Appendices A1-A11 (cited in the headers of the imported TTR_base.v, TTR_types.v, TTR_records.v). | 18/18 | partial | 3 major restructuring | ii, iv, v | — |
| ttr_mtt/TTR_theorems_shallow.v | Cooper, R. (2005). Records and record types in semantic theory. Journal of Logic and Computation 15(2):99-112.; Cooper, R. (2012). Type theory and semantics in flux. In Handbook of the Philosophy of Science 14: Philosophy of Linguistics, 271-323. | 12/12 | partial | 3 major restructuring | ii, iv | — |
| ttr_mtt/TTR_types.v | Cooper, R. (2023). From Perception to Communication: A Theory of Types for Action and Meaning. Oxford University Press. Appendix A2-A8. | 10/10 | partial | 3 major restructuring | i, ii, iv | — |

## type-logical grammar

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| atlas/type_logical/Lambek.v | Lambek, J. (1958). The mathematics of sentence structure. Amer. Math. Monthly 65(3):154-170.; Moot, R. & Retoré, C. (2012). The Logic of Categorial Grammars. LNCS 6850. Ch. 2-3. | 40/40 | faithful | 1 as-is | ii, iv, v, iii | — |

## type-theoretic (MTT individuation)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| extras/indi.v | Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. ISTE/Wiley. Relevant: ch.5 'Copredication and Individuation' -- s.5.2 dot-types (Def 5.1 components, formation rule with C(A) cap C(B) = empty, (5.11)-(5.12)), s.5.3 (5.13) setoids, (5.15), s.5.3.1 (5.21)-(5.26) and Def 5.2 sub-setoid, s.5.3.2 Def 5.3 Three_0 (5.27) and Def 5.4 Three (5.34), s.5.3.3 (5.41)-(5.48) with Def 5.5 pre-setoids and Def 5.6 THREE, s.5.3.4 (5.49)-(5.60) adjectives; s.5.4 pp. 122-125 Liebesman & Magidor (5.69)-(5.80), fn 14; s.6.3.2 'Copredication and individuation in Coq' pp. 146-149, (6.3), (6.4), fn 12 p.142; Appendix A7.9 'Individuation' pp. 200-207 (the direct textual origin of l.1-236); Appendix 6 rules for dot-types.; Luo, Z. (2012). Common Nouns as Types. LACL 2012, LNCS 7351, pp. 173-185. Cited by the book (s.5.3 p.109, as Luo 2012a) as the origin of the 'CN = type + identity criterion' proposal; background only, the file encodes nothing specific to it. (source gap) | 20/20 | faithful | 2 slight modification | ii, iv | ttr_mtt/Book_Individuation.v |

## type-theoretic (MTT quantifiers)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/quanrifiers2.v | Barwise, J. & Cooper, R. (1981). Generalized Quantifiers and Natural Language. Linguistics and Philosophy 4(2): 159-219. (Sec. 1.2-1.5, 2.5 S5-S6, 4.4 lives on, 4.5 Table I, 4.7 monotonicity, Appendix B SP1-SP6, Appendix C.); Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. ISTE/Wiley. (Sec. 3.1 (3.12)-(3.13) and Table 3.1; Sec. 5.3.2 Defs. 5.3-5.6; Sec. 6.3 with footnote 12 on CN := Set; Appendix A7.1 some/all/no, A7.7 three_0.) (source gap) | 5/5 | unfaithful | 2 slight modification | iv, ii, iii | /Users/graogro/Dropbox/revisiting-formal-semantics/extras/Quantifiers.v |

## type-theoretic (MTT)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/AdjectivesExtension.v | Chatzikyriakidis, S. & Luo, Z. (2013). Adjectives in a Modern Type-Theoretical Setting. In Morrill & Nederhof (eds.), FG 2012/2013, LNCS 8036, pp. 159-174. Springer.; Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. ISTE/Wiley. Section 3.3 'Adjectival modification: a case study' (pp. 65-74, Table 3.2, (3.88)-(3.127)) and Appendix A7.3-A7.4 (pp. 194-196, Coq code for intersective/subsective and privative adjectives). (source gap) | 12/12 | partial | 2 slight modification | ii, iii, iv | — |
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/MTT_base.v | Luo, Z. (2012). Common Nouns as Types. LACL 2012, LNCS 7351, pp. 173-185. Used: Fig. 1 (p.175), s.2 'CNs as Types in Formal Semantics' (pp.175-176), s.3 'Criteria of Identity' (pp.177-180, Passenger[T] Sigma-types), s.4 'Proof Irrelevance and Identity for Modified CNs' (pp.180-181), s.5 mass nouns.; Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. ISTE/Wiley, 240 pp. Used: s.2.3.2 universe CN and (2.20)-(2.22); s.2.4 coercive subtyping ((2.38), rules CA/CD, coherence fn 18); s.3.1 Table 3.1, (3.1)-(3.16); s.3.2.2 (3.30)-(3.33); s.3.3.1 (3.88)-(3.97) and the two adequacy conditions (pp.68-69, fn 20-21); s.3.3.2 (3.102)-(3.104); s.6.3 'MTT-semantics in Coq' (pp.142-144, fn 12); Appendix A7.1 (p.193) and A7.3 (pp.194-195). (source gap) | 2/2 | partial | 2 slight modification | ii, iv | /Users/graogro/Dropbox/revisiting-formal-semantics/extras/MTTbase.v |
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/MTTbase.v | Luo, Z. (2012). Common Nouns as Types. LACL 2012, LNCS 7351, pp. 173-185.; Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. ISTE/Wiley (240 pp.). Relevant: sec. 1.4.1 (Table 1.3, (1.9)-(1.10)), 2.3.2 (universe CN, (2.20)-(2.22)), 2.4 (coercive subtyping, (2.38)-(2.42)), 3.1 ((3.1)-(3.16)), 3.2.1-3.2.2 ((3.21), (3.30)-(3.33)), 3.3.1-3.3.2 ((3.88)-(3.105)), 6.3 (ch.6 fn.12), Appendix A7.1/A7.3. (source gap) | 2/2 | partial | 2 slight modification | ii, iv | extras/MTT_base.v |

## type-theoretic (mass/count)

| File | Source | Proved/Total | Faithful | Determination | Artifacts | Dup of |
|---|---|---|---|---|---|---|
| /Users/graogro/Dropbox/revisiting-formal-semantics/extras/mass.v | Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern Type Theories. ISTE/Wiley, 240 pp. The assigned 'mass/count chapter' does not exist: the TOC (chs. 1-7) has no mass/count chapter or section, and the full extracted text contains 'mass' only in 'UMass, Amherst' (Carlson 1977 bibliography entry) and in the bibliography entry for Link 1983; 'count noun', 'measure phrase', 'grinder', 'partitive' never occur. Relevant only as the origin of the framework mass.v inherits through indi.v: ch. 5 s.5.3 'Identity criteria: individuation and CNs as setoids' pp. 108-119 ((5.13)/(5.15) CN = setoid (A, =A) p.109; s.5.3.1 p.110: ICs are needed precisely for numerical quantifiers 'bigger than one', fn 7 IC-respecting predicates; Def 5.3 Three_0 p.112 = indi.v's three_f; Def 5.4 Three p.113; Def 5.6 THREE p.116), s.6.3.2 pp. 146-149 and Appendix A7.9 'Individuation' pp. 200-207 (the Coq code that indi.v transcribes).; Link, G. (1983). The logical analysis of plurals and mass terms: A lattice-theoretical approach. In Baeuerle, Schwarze & von Stechow (eds.), Meaning, Use, and Interpretation of Language, de Gruyter, 302-323; on disk as the reprint in Portner & Partee (eds.) 2002, Formal Semantics: The Essential Readings, ch. 4, pp. 127-146 (complete, 20 pages, image-only scan, read as page images). Mass-term apparatus: cumulative reference (10) p.128; constitution relation \|> and materialization function h p.128; star operator, E a complete atomic Boolean algebra, atoms A, i-sum a (+) b vs material fusion a + b, i-part (15) p.130; sigma (17), mu material fusion (18), m-part T (19), D a complete join-semilattice with (20) p.131; h : E\{0} -> D a semilattice homomorphism (21), <=m (22), mass predicates denote join-closed subsets of D, mass term correspondent mP (23), (24)-(26) p.132; Distr (27) p.133; minimal-parts caveat and (43)-(44) p.134; (45)-(46), LPM syntax with the disjoint predicate classes MT / DP p.135; (D.8)-(D.21) incl. Mpa (D.11), mP (D.13), M(P) (D.20) p.136; boosk (D.22), <=m (D.23), ~m (D.24), model (D.25) pp.137-138; (D.26)-(D.32), (49)-(59) p.138; (60)-(64) and theorems (T.1)-(T.32) incl. (T.12) cumulativity for P in MT, (T.13)-(T.14) p.139; s.3 CN subcategorized into MCN / SCN / PCN p.140; translations 1-11 incl. 'some water' (5), 'all water' (11) and the numerals remark p.141; summary (1)-(4) p.144. (source gap) | 3/3 | unfaithful | n/a | ii, iii, iv | — |

## Framework-comparison edges

Grades per phenomenon, from bridge theorems: 5 definitional / 4 equivalence / 3 one-way or mediated / 2 divergent (countermodel) / 1 after re-encoding. Similarity = mean grade over jointly attempted phenomena; overlap = Jaccard of attempted phenomenon sets.

| Edge | Level | Bridge | Similarity | Overlap | Joint | A-only | B-only |
|---|---|---|---|---|---|---|---|
| lambek__discocat | intra-family | — | 3.0 | 0.33 | 2 | 2 | 2 |
| mtt__ranta | intra-family | atlas/mtt_ranta/MTT_vs_Ranta.v | 4.2 | 0.56 | 10 | 5 | 3 |
| ptq__barwise_cooper | intra-family | atlas/montague/PTQ.v | 4.33 | 0.43 | 3 | 2 | 2 |
| ptq__kratzer | intra-family | shallow/kratzer2.v | 4.0 | 0.43 | 3 | 2 | 2 |
| ptq__lambek | cross-family | atlas/montague/PTQ_vs_Lambek.v | 5.0 | 0.5 | 4 | 2 | 2 |
| ptq__mtt | cross-family | atlas/montague/PTQ_vs_MTT.v | 2.83 | 0.55 | 6 | 2 | 3 |
| ranta__dts | intra-family | atlas/mtt_ranta/DTS.v | 4.2 | 0.62 | 5 | 1 | 2 |

## Paper assessment (200-paper survey)

| Category | Papers |
|---|---|
| A | 78 |
| B | 52 |
| C | 50 |
| D | 50 |

## Formalizability levels (evidence-based; rubric §5)

| Level | Meaning | Papers |
|---|---|---|
| F0 | surveyed only (A-D prediction, no source on disk) | 86 |
| F1 | sourced (PDF/djvu on disk) | 90 |
| F2 | designed (design doc maps its content) | 21 |
| F3 | piloted (some Coq exists; record may be partial) | 13 |
| F4 | formalized (atlas-standard file, audited record) | 9 |
| F5 | verified & connected (verify agrees and/or in a graded edge) | 11 |

### Survey prediction vs actual determination (findings)

| Paper | Predicted | Determined | Level |
|---|---|---|---|
| Kamp, H. (1981) - "A Theory of Truth and Semantic Representation" (DRT | as_is | not_applicable | F3 |
| Heim, I. (1982) - "The Semantics of Definite and Indefinite Noun Phras | as_is | slight_modification | F3 |
| Barwise, J. & Cooper, R. (1981) - "Generalized Quantifiers and Natural | as_is | major_restructuring | F3 |
| Champollion, L. (2017) - "Parts of a Whole: Distributivity as a Bridge | as_is | slight_modification | F3 |
| Rooth, M. (1992) - "A Theory of Focus Interpretation" | as_is | slight_modification | F3 |
| Chatzikyriakidis, S. & Luo, Z. (2013) - "Natural Language Inference in | as_is | slight_modification | F3 |
| Luo, Z. (2012) - "Common Nouns as Types" | as_is | slight_modification | F3 |
| Chatzikyriakidis, S. & Luo, Z. (2014) - "Adjectival and Adverbial Modi | as_is | not_applicable | F3 |
| Bekki, D. (2014) - "Representing Anaphora with Dependent Types" | as_is | slight_modification | F5 |
| Chatzikyriakidis, S. & Luo, Z. (2017) - "Modern Perspectives in Type-T | as_is | not_applicable | F3 |
| Luo, Z. (2010) - "Type-Theoretical Semantics with Coercive Subtyping" | as_is | not_applicable | F3 |
| Bekki, D. & Mineshima, K. (2017) - "Context-Passing and Underspecifica | as_is | slight_modification | F5 |
| Cooper, R. (2005) - "Records and Record Types in Semantic Theory" | as_is | major_restructuring | F3 |
| Coecke, B., Sadrzadeh, M. & Clark, S. (2010) - "Mathematical Foundatio | major_restructuring | as_is | F5 |
