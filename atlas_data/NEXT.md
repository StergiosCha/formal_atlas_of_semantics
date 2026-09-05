# Continuing FORMAL-ATLAS on Azure credits

Run each item as its **own** Claude Code session, on Fable via Foundry:

```bash
source ~/claude-azure.sh && cd ~/Dropbox/revisiting-formal-semantics && claude --model fable
```

Rules that keep the cost at ~$30-80 per session (the earlier blow-up was caused
by parallel subagents each re-reading the PDFs):

* **No subagents, no workflows.** Say so in the prompt if the session reaches for them.
* One file per session; it must compile before the session ends; commit after.
* Consult a PDF only for a specific definition — the design doc already digested it.
* Model after `atlas/type_logical/Lambek.v`: header with sources / what is and is
  not formalized / artifact classes, source reference on every definition and
  theorem, `Print Assumptions` block at the end, zero `Admitted`.

Compile command (from the repo root):

```
coqc -R shallow "" -R deep "" -R extras "" -R ttr_mtt "" -R atlas "" atlas/<dir>/<File>.v
```

Add the file to `_CoqProject`, then `coq_makefile -f _CoqProject -o Makefile && make -k -j8`.

## Queue

(Reordered 2026-09-05 by the user: the MTT/TTR/Ranta strand comes before
RSA/DisCoCat/DRT.)

- ~~**DPL** — `atlas/dynamic/DPL.v`~~ DONE 2026-09-05: compiled, committed,
  record `atlas__dpl.json` written (18 theorems axiom-free, 9 classic-only,
  6 funext; d34/fact6 misprints refuted).
- ~~**InqB** — `atlas/inquisitive/InqB.v`~~ DONE 2026-09-05: 2445 lines,
  zero Admitted, all 13 audited theorems closed under the global context
  (fully constructive — no extensionality needed after all), committed,
  record `atlas__inqb.json` written.

- ~~**MTT + Ranta pair**~~ DONE 2026-09-05: `atlas/mtt_ranta/{MTT,Ranta,
  MTT_vs_Ranta}.v` all compile, zero Admitted, zero axioms (14+14+15
  audited theorems closed under the global context); committed; records
  written; design `designs/mtt_ranta.md`. Headline bridge findings: the
  shared core (CNs, every/no, donkey) agrees DEFINITIONALLY; the genuine
  divergence is proof relevance (Sigma vs Prop-exists, mediated by
  `inhabited`); subtyping is MTT-only, sugaring is Ranta-only.

DONE 2026-09-05 late session ("do all" #2, ultracode):
- **DisCoCat.v** DONE: 1637 lines, 98 theorems, zero Admitted/axioms,
  all 25 audited theorems closed; F_deq soundness over the whole
  compact closed equational theory; all CSC10 §4-5 numbers reproduced
  by vm_compute; record atlas__discocat.json; edge lambek__discocat
  (bridge file = future work: formalize CGS13's translation).
- **24 audit records backfilled** by a parallel workflow (every .v in
  _CoqProject now has a record — 64 total). Notable findings recorded:
  shallow/PTQ.v's temperature_puzzle is Admitted AND misformulated
  (refutable as stated over Parameters); its seek_ambiguity is vacuous;
  the ttr_mtt pilots have no subtyping theorems. Records are in
  records/ (batch-swept; spot-check the extras ones when promoted).
- **designs/ttr.md and designs/drt_dpl.md written** (the workflow's
  design agents stalled; written by hand): TTR adopts DEEP labelled
  records (assoc lists, width+depth subtyping decidable, meet theorem,
  MTT hooks); DRT_DPL reuses the committed DPL.v models and proves
  verifies <-> sem(tr K) by mutual induction, donkey inherits
  dk2_truth.
- **tool/ scaffold committed** (Semantics Workbench v0): FastAPI coqc
  checker with the atlas precompiled (Docker), GUIDE-based LLM
  draft-and-check loop; frontend map/phenomenon views = next.
Queue now: TTR.v build (design ready) -> DRT_DPL.v build (design
ready) -> tool frontend -> Lambek->pregroup bridge (CGS13) ->
paper §§4-5 from atlas.json (the edge matrix is the comparison
section).

Earlier same-day batch: items 1-3 below are
built — edges/ schema + consolidate/build_site support + 6 graded edges
(similarity/overlap matrix in ATLAS.md and atlas.json); Montague lineage
trunk `atlas/montague/PTQ.v` + Coq edges PTQ_vs_Lambek.v (grade 5.0) and
PTQ_vs_MTT.v (2.83) + JSON edges to Kratzer and Barwise&Cooper;
`atlas/mtt_ranta/DTS.v` (Bekki; caveat: B14/BM17 PDFs still missing from
papers/ — spot-check refs when added); GUIDE.md (reading protocol for
semi-formal papers, Giannakidou worked example). Remaining from the
batch: nothing. Next per user: RSA, then DisCoCat, then TTR, then
DRT≈DPL; also promote shallow/PTQ.v extras (tense/analysis trees) and
re-audit kratzer2.v / BarwiseCooper.v to atlas standard (their edge
JSONs carry caveats).

1. **Comparison methodology + scoring (user proposal 2026-09-05).** Three
   levels: (a) intra-family bridges (MTT_vs_Ranta done), (b)
   representative vs representative across families (one MTT repr vs one
   Montagovian repr), (c) family vs family aggregates. Score per
   phenomenon on a fixed checklist (quantification, anaphora/donkey,
   adjectives, modality, copredication, subtyping, generation, tense,
   questions, ...), grades derived from the bridge THEOREMS:
   5 definitional (reflexivity) / 4 provable equivalence / 3 one-way or
   mediated (e.g. inhabited) / 2 statable but divergent (countermodel) /
   1 statable only after re-encoding / 0 not statable (not looking for
   the same thing). Two aggregates per pair: similarity = mean grade
   over jointly-attempted phenomena; coverage overlap = Jaccard of
   attempted sets. Storage: `atlas/edges/<a>__<b>.json` with grades +
   theorem names as evidence; consolidate.py to aggregate a similarity
   matrix onto the site. Needs: edge schema + consolidate/build_site
   support + backfill of the MTT_vs_Ranta edge.
2. **Montague lineage (user proposal 2026-09-05).** PTQ as the trunk +
   one edge file per descendant, each with the graded comparison above:
   promote a canonical `atlas/montague/PTQ.v` (audit/rebuild from
   shallow/PTQ.v, deep/PTQ_deep2.v, theorems_PTQ); then edges,
   materials-first order: PTQ↔Barwise&Cooper GQ (extras/BarwiseCooper.v
   exists), PTQ↔Kratzer (extras/kratzer* exist), PTQ↔Lambek (the
   Lambek.v fragment already computes Montague meanings), PTQ↔MTT
   (mtt_ranta pair done), PTQ↔DPL (dynamic turn), PTQ↔Heim/FCS
   (extras/FCS*.v exist), later PTQ↔DisCoCat. Design doc first
   (designs/montague_lineage.md) fixing the shared fragment sentences.
3. **Bekki/DTS** — third node of the type-theoretic cluster
   (`atlas/mtt_ranta/DTS.v` + edge): Dependent Type Semantics = the
   dynamic/anaphoric branch from Ranta (underspecified @-terms, anaphora
   resolution as proof search, presupposition via type checking; Bekki
   2014 LACL, Bekki & Mineshima 2017). Key formalizable claim: DTS
   resolution GENERALIZES Ranta's pronominalization — the donkey @-term
   admits the projection resolution as one solution (and ambiguity =
   multiple resolutions). Needs the papers in papers/foundations/ first.
4. **TTR** — `atlas/ttr/TTR.v`. **No design doc yet** — from Cooper 2023
   (From Perception to Communication). Record types, dependent record types,
   subtyping of records; successor to the `ttr_mtt/TTR_*.v` pilots.
   Possible fourth comparison file against MTT later (C&L ch. 1 discuss
   TTR explicitly).
- ~~**RSA** — `atlas/probabilistic/RSA.v`~~ DONE 2026-09-05: 1898 lines,
  117 theorems, zero Admitted, zero axioms, all 23 audited theorems
  closed; every probe value reproduced exactly; two source misprints
  recorded (GF16 Box 1 cost sign; LG17 eq. 20 ~.015 vs exact 1/6486).
  Record atlas__rsa.json. STRETCH remainder (lexical uncertainty/Horn,
  Bergen closed form 1/(2n+2), threshold semantics) planned in
  designs/rsa.md T36-T45 if ever wanted.
6. **DisCoCat** — `atlas/categorical/DisCoCat.v`, design `.../discocat.md`. Hardest.
   Coecke, Sadrzadeh & Clark 2010: free pregroup reductions, a concrete
   finite-dimensional model over `Q`, the snake equations, functoriality, one
   computed sentence.
7. **DRT ≈ DPL** — `atlas/dynamic/DRT_DPL.v`. **No design doc yet** — write one first
   from Muskens 1996 and Kamp/van Genabith/Reyle 2011, then the file. Needs DPL (done).
   Headline: `f verifies K yielding g  <->  (f,g) ∈ ⟦tr(K)⟧`. This is the paper's
   cross-framework edge.

Then, cheaply (these can share one session each):

6. Audits for the 23 files without a record in `atlas/records/` (see `ATLAS.md` for
   which). Short prompt, one file per call, schema as in an existing record.
7. Dedupe the duplicate groups into `extras/attic/`, fix `_CoqProject`, add GitHub
   Actions CI (`coq-community/docker-coq-action@v1`, coq_version 8.20), rewrite the
   READMEs from the records.
8. Fill sections 4-5 of `paper/atlas_paper.tex` from `atlas/atlas.json`.

After each file: write its record to `atlas/records/atlas__<key>.json` (copy the shape
of `atlas__lambek.json`), then

```bash
cd ~/Dropbox/formalizing_formal_semantics && python3 atlas/consolidate.py && python3 atlas/build_site.py
```

and republish `atlas/site/index.html` to the artifact URL in the memory file.
