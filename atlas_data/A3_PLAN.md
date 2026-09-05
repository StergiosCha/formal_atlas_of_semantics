# A3 — verifier pass: state and plan

Started 2026-09-05. `verify.py` exists and has run over all 64 records.
This file is the handover: what is now measured, what it proved, and the steps
left. Steps 6-7, the L2/L3 revisions, and the three closing sections came out
of a five-lens design review (proof engineering, learning science, NeSy
research, hostile audit, citability) run the same day.

---

## What landed

`atlas/verify.py` — mechanical verification. Per file it runs `coqc` fresh,
then `Print Assumptions` on every proved theorem via one `Redirect` file each,
then a comment-stripped parse for the declaration census. Output goes to
`records/<key>.mech.json`. 64 files in ~3 minutes; the atlas layer alone in 21s.

```bash
cd atlas && python3 verify.py          # atlas/*/*.v
python3 verify.py --all                # every file in _CoqProject
python3 verify.py atlas/dynamic/DPL.v  # one file
```

### The headline result

| | files | theorems | proved | admitted | top-level axioms | undocumented axioms |
|---|---|---|---|---|---|---|
| `atlas/` | 12 | **714** | **714** | **0** | **0** | **0** |
| pre-atlas | 52 | 342 | 329 | 9 | 556 | 335 distinct |

The atlas layer's central claim is now Coq's verdict rather than the auditor's.
All 64 files compile. DPL's 37 non-closed theorems depend on exactly two
documented axioms — `Classical_Prop.classic` (29×) and
`FunctionalExtensionality.functional_extensionality_dep` (8×) — which is
precisely what ROADMAP claimed and nothing more.

The 556-vs-0 axiom split is the sharpest argument yet for Track C's
`extras/attic/`: the pre-atlas files are `Parameter`-heavy shallow embeddings,
which is why 335 distinct axioms appear and why so many report `closed=0/N`.
They are raw material and the site should never let them be mistaken for
audited work.

### Disputes already found

- `atlas__ptq`: record says `counts.theorems: 16`; measured 19. The record's own
  `theorems[]` prose enumerates all 19 by name, so the *prose is right and the
  count field is wrong*. Same shape in `atlas__dpl`: claims 168, measured 171.
- Aggregate `atlas.json` `stats` say 1045 theorems / 12 admitted; measurement
  says 1056 / 9. The admitted gap is mostly `extras/FCS2.v` (record claims 5,
  Coq finds 2). Reconcile before the site quotes either number again.
- 41 of 64 files carry at least one dispute — nearly all are count drift, not
  substance.

### Fixed in passing

`consolidate.py` skipped `*.verify.json` but would have ingested the new
`*.mech.json` sidecars as if they were audit records, silently doubling the
record count to 128. Now skips both.

---

## What is left

**1. Reconcile the counts — DONE (2026-09-05), and the hand-check paid off.**
Both suspicious discrepancies were the *parser's* fault, not the records':
`extras/FCS2.v` really has 5 Admitted (3 are admitted `Definition`s — axioms
in disguise the parser didn't track), and the lone `unparsed_status` was
`Abort All.`, a terminator form the regex missed. Both fixed in verify.py.
Reconciliation is an **overlay in consolidate.py**, not record edits: measured
counts win at merge time, the auditor's claim stays visible as
`counts_claimed`, and the record files are never touched. Had we
blanket-overwritten, correct auditor data would have been destroyed by wrong
parser output — the strongest possible argument for the overlay design.
Post-fix aggregate: 1056 theorems, 1043 proved, 12 admitted (9 theorems +
3 admitted definitions) — which *validates* the original claimed 12.

**2. Emit `records/<key>.verify.json` (the schema already exists).**
`consolidate.py:40-51` has been waiting for a producer since it was written:
`{agrees, disputes[], confidence, revised_faithfulness?, revised_determination?}`.
Keep the mechanical and semantic passes separate and honest:
- `.mech.json` answers *does it compile, is it axiom-free, are the counts right*
  — deterministic, no opinions.
- `.verify.json` answers *is the faithfulness verdict defensible* — needs a
  reader with the source paper.
A `.verify.json` derived only from mechanical facts must say so in
`confidence`, or the F5 badge ("verify agrees") overclaims. This is the one
place where cutting a corner would undo the point of A3.

**3. Semantic pass, atlas layer only.** 12 records, sources on disk. One agent
per record re-reads the `.v` file plus the record and adversarially checks the
faithfulness/determination verdicts and the `source_gap` claims. Do not attempt
this for the 52 pre-atlas records or the ~101 survey entries with no PDF —
`log` what was skipped rather than letting silence imply coverage.

**4. Surface it on the site — DONE (2026-09-05).** Theory pages now carry a
MACHINE VERIFICATION block: coqc version, assumption-closed N/N, the named
axioms, unsafe flags in rust if any ever appear, and a "record claimed X"
line whenever the audit's numbers drift from measurement. Records without a
mech sidecar get a rust "Self-reported only" banner instead. Original spec:
The green check has to mean something specific.
Show per-theory: compiled ✓, N/N closed under the global context, the named
axioms where not closed, and the coq version it was checked with. A file that
is merely *self-reported* clean must look different from one Coq confirmed.
Rust, not green, for anything disputed.

**5. Wire into CI — WRITTEN (2026-09-05), untested against GitHub runners.**
`.github/workflows/verify.yml`: compile → `coqchk` kernel recheck (18 s
locally for the whole atlas layer) → `verify.py --all && --lock` →
`git diff --exit-code` on records + lock (drift IS the failure, reviewable as
a diff) → an atlas-invariants gate (no Admitted, no top-level axioms, no
undocumented axioms, no unsafe flags, no unresolved queries — passes clean
locally). mech.json is machine-independent (checkout paths stripped) and a
mirror-position run reproduces committed records byte-for-byte, so the diff
gate is sound. First real push will shake out runner quirks (the
`sudo chown` line, apt in the coq container). Original spec:
GitHub Actions: `make -k -j8` then
`python3 verify.py --all`, failing the build on a new admitted, a new
undocumented axiom in `atlas/`, or a compile break. That makes A3
self-maintaining instead of a snapshot, and it is what lets the badge stay
honest between sessions. Three cheap hardenings, none needing an LLM:
- **`coqchk` on the `.vo` set.** Everything above trusts `coqc`; `coqchk`
  independently revalidates the kernel terms and emits its own axiom census,
  cross-checking `Print Assumptions`. One CI line, minutes of runtime, and the
  claim upgrades from "coqc accepted it" to "the kernel checker rechecked it".
- **Commit the `.mech.json` files and diff measured-vs-committed in CI.** They
  are deterministic, so drift shows up as a reviewable PR diff instead of a
  red wall of coqc output.
- Lint for the unsafe flags (`-type-in-type`, `Unset Guard Checking`, etc.)
  in files and `_CoqProject` — the one hole `Print Assumptions` cannot see.

**6. Statement fingerprints + `claims.lock` — DONE (2026-09-05).**
`verify.py` now emits `Check @<fqname>` per proved theorem in the same
Redirect driver, hashes the normalized statement, and `--lock` writes
`atlas/claims.lock`: **714 claims pinned** (fqname → statement_sha, file,
since, status; vanished theorems become `deprecated`, never dropped).
Original rationale, kept for the record:
Everything above fails CI on a new `Admitted` or axiom — but a theorem's
*statement* can be silently weakened (`<->` downgraded to `->`, a hypothesis
added, a `forall` narrowed) while its name, the counts, and axiom-freedom all
stay green. The 7 edges and 64 records cite theorems by name; nothing
mechanical ties an edge's grade to the statement as it exists at HEAD. Fix, in
the Redirect driver verify.py already generates: emit `Check @<fqname>.` per
proved theorem (never `Print` — it dumps proof terms), normalize whitespace,
hash, and pin the hashes in a committed `atlas/claims.lock` mapping
`fqname -> {statement_sha, since_tag, status: active|deprecated}`. CI fails on
any hash change without a lock update, which forces statement changes to be
deliberate, reviewed, and released — the precondition for anyone citing a
theorem from a two-year-old paper. ~1 day, zero LLM calls. With one maintainer
and LLM-assisted editing (L3 will rewrite files), silent statement drift is
the realistic failure mode, and this is the only step that catches it.

**7. Retire the regex census: one SerAPI/coq-lsp pass, three consumers.**
The Notes below are a list of regex landmines that already bit once each.
HOSTING.md §2 already plans a sentence-by-sentence SerAPI dump for the
Proof-General reader; make that same AST-level artifact the source for (a) the
declaration census, (b) the proof states, and (c) the per-theory signature
manifests (see the loop section). Until it lands, differentially check the
regex parser against it in CI so the two can never silently disagree. Build it
once, use it three times — the parser stops existing as a thing that can drift.

---

## Where the LLM belongs

One rule, and it is the whole architecture: **the LLM proposes, Coq disposes.**
The model never issues a verdict that ends up in a record. It generates a
candidate Coq artefact; `coqc` decides; the compiler's answer is what gets
written. This is the same draft-and-check loop as B4 and reuses `tool/`'s
checker container, so A3 doubles as the first real load test for it.

**L1. Theorem ↔ source-claim alignment (highest value).** We now have 714
verified theorem *names* and 64 records whose `theorems[]` are prose glosses
like `"qsum/qpow/normalize algebra (T1-T2, 20+ lemmas)"`. Nothing links a Coq
identifier to a numbered result in the paper. No regex can: it needs reading.
One agent per file, given the `.v` source, the record and the paper, emits
`{coq_name, paper_result, confidence}` triples. That mapping is what lets the
site say *"`box_K` is PTQ meaning-postulate M73-T4"* instead of just listing
identifiers, and it is the substrate every edge grade should have been resting
on. Anything below high confidence stays unlinked rather than guessed.

**L2. Vacuity detection — LLM drafts, Coq refutes.** A theorem can be `Qed`-clean,
axiom-free, and still worthless: contradictory hypotheses make anything
provable, and a `Definition` that unfolds to `True` makes a headline theorem
trivial. Nothing in the current pipeline would notice, which is the single
biggest hole left in the "714/714 proved" claim. For each flagged theorem the
LLM drafts a probe:

```coq
Lemma probe_vacuous : <hypotheses of T> -> False.
```

If `coqc` proves it, the hypotheses are unsatisfiable and `T` is vacuous —
a machine-checked refutation, not an opinion. Run the same trick for
triviality (`<conclusion of T>` provable with the hypotheses discharged).

*Status 2026-09-05: the Ltac2 probe machinery below is being built
(`probes/VacuityProbe.v` + `probes/run_probes.py`, output to
`records/<key>.probe.json`); results not yet in.*

**Revision (design review): make probe *generation* symbolic too.** Routing
probe generation through the LLM contradicts the propose/dispose rule for no
gain and caps coverage at ~30 theorems purely for budget. Ltac2 ships in Coq
8.20 core (stdlib-only constraint holds): one tactic that walks a statement's
Prod telescope via `Constr.Unsafe.kind`, splits binders from Prop premises,
and mechanically builds the probe goals — non-vacuity witness
(`exists <binders>, H1 /\ ... /\ Hn`), vacuity (`... -> False`), triviality
(conclusion sans hypotheses). Full 714-theorem coverage, no LLM calls, no cap.
The LLM's only remaining role in L2 is the residue: probes Ltac2 builds but no
automatic tactic settles, where a drafted witness or refutation is worth a few
calls. 2-3 days of fiddly-but-standard Ltac2; removes L2's budget risk entirely.

**L3. Axiom triage for the attic — scoped down (design review).** Full triage
of all 335 pre-atlas axioms is the worst value on this list: those files are
headed to `extras/attic/` regardless, so classifying every axiom polishes
material the project is about to demote. Do a *sample of ~20* — enough for the
paper's narrative about what shallow `Parameter`-heavy embeddings cost — via
the original mechanism (LLM classifies: ontological primitive / dischargeable
laziness / theorem-trivialising cheat; drafts discharging proofs for the
middle bucket; `coqc` accepts or rejects). Stop there. The 556-vs-0 table is
already the argument for the attic; it does not need 335 case studies.

**L4. Semantic faithfulness (this is step 3 above).** Adversarial, not
single-shot: three verifiers per record with distinct lenses — *does the Coq
statement say what the paper's theorem says*, *do the omissions listed change
the result*, *is the `source_gap` claim actually a misprint and not our
misreading*. Majority refutes ⇒ dispute. A single agreeable reader is worth
nothing here; the failure mode is politeness, not ignorance.

**L5. Dispute narration.** 41 flagged files, mostly count drift. LLM writes the
one-line explanation per dispute for `.verify.json`; a human skims 41 lines
instead of 41 diffs. Same job in CI: turn a red build into "DPL.v gained an
`Admitted` at line 812" rather than a wall of coqc output.

**Costs and caution.** L1 and L4 are ~64 and ~36 agent calls, cheap and safe.
L2 is the one that can burn budget — probe generation is iterative and most
probes correctly fail. Cap it: one retry per theorem, cache by statement hash,
and `log` how many theorems were skipped so partial coverage never reads as
full coverage. And keep the LLM's output out of `.mech.json` entirely — that
file is Coq's testimony and must stay uncontaminated. Model-derived judgements
belong in `.verify.json`, tagged with which of L1-L5 produced them.

---

## The neurosymbolic loop, and why A3 is what makes it teachable

The atlas is not an audit artefact that happens to have a website. It is an
**educational research tool**: the thing a student opens to find out *why* a
semantic theory can or cannot say something, and the thing a researcher cites
when claiming two frameworks agree. A3 is the precondition for both — an
unverified corpus can neither teach nor be cited.

### The loop

Neural proposes, symbolic disposes, and the symbol's complaint is fed back as
structure rather than prose:

```
student's English claim
   │
   ├─▶ [LLM] draft a Coq statement against theory T's vocabulary
   │        │
   │        ▼
   │   [coqc / tool/ checker]  ──▶  PROVED ──────────────▶ show proof + goal states
   │        │
   │        ├─ type error ─────┐
   │        ├─ unbound ident ──┤
   │        ├─ tactic failed ──┼──▶ [symbolic feedback extractor]
   │        └─ unsolved goal ──┘         │  typed error + goal state +
   │                                     │  the theory's actual signature
   │        ◀────────────────────────────┘
   │      repair (bounded: 3 attempts, then stop and say so)
   │
   └─▶ after N failures: NOT STATABLE — and *prove* it by showing the
        vocabulary of T contains no constant of the required type
```

The part that matters, and that most LLM-prover demos get wrong: **the feedback
must be symbolic, not stderr.** Do not paste `coqc` output back into the prompt.
Parse it into a typed signal — `{kind: unbound_identifier, name: "believe",
available: [...T's actual constants...]}` or `{kind: unsolved_goal, goal: <the
goal state>, hyps: [...]}` — and feed that. The available-constants list is what
turns a failure into a lesson: *DPL has no modal operator, which is why your
sentence cannot be written*, rather than *error at line 3*.

**Known violation to fix:** `tool/llm/loop.py` currently does
`feedback = f"coqc failed:\n{resp['output'][-4000:]}"` — the raw stderr tail,
exactly what this section forbids. The shipped scaffold predates the rule;
replace it when the typed extractor lands, and keep both code paths, because
the difference between them is a measurable experiment (see below).

**The vocabulary must be an artifact, not a gesture.** Ship
`signatures/<theory>.json` — every exported constant with its type, dumped from
the same SerAPI pass as step 7. It is simultaneously (a) the evidence behind a
NOT-STATABLE verdict, (b) the `available:` list in the typed feedback, and
(c) a browsable "what can this theory even talk about?" page — arguably the
most educational page the site could have. A NOT-STATABLE without a signature
manifest behind it is a guess wearing a badge.

We already have the goal states. `HOSTING.md` §2 dumps every sentence's goal
state in CI as a build artefact, so the repair loop and the Proof-General
reader read the **same** data structure. The loop costs no extra server.

### Why A3 is the precondition

The loop can only ever be as honest as the corpus it checks against. Three
concrete dependencies:

- **`NOT STATABLE` needs a verified vocabulary — and a mechanism, not
  exhaustion.** The loop diagram above reaches NOT-STATABLE "after N failures",
  which violates the iron rule at the tool's most citable feature: repeated
  LLM failure is evidence about the LLM, not about the theory. The design
  review's highest-scored idea fixes this with a **two-tier verdict**:
  - *Tier 1, machine-checked:* `NOT_STATABLE_SIGNATURE` — the required
    constant/type simply isn't in the theory's signature manifest, and a
    generated `Fail Check (...)` probe compiled against the theory confirms
    the term cannot even be *typed*. Coq's testimony, with a receipt. Honest
    scope caveat, stated wherever shown: this establishes no *primitive* of
    the required type exists, not that no lambda-definable encoding could —
    inexpressibility-in-principle is a theorem we mostly don't have.
  - *Tier 2, bounded search:* `NOT_STATED_AFTER_N_ATTEMPTS` — drafting failed
    N times. Labeled as exactly that, never conflated with tier 1.
  Every tier-1 verdict needs a positive control (a nearby claim that IS
  statable, compiling against the same manifest) so an over-eager signature
  check can't quietly mark everything unstatable. Claiming "DPL cannot express
  this" is only defensible with the signature manifest + probe receipt behind
  it; without A3 it is a guess dressed as a verdict.
- **`NEEDS ASSUMPTION` needs the axiom census.** Naming the missing assumption
  means naming it *from the file's actual axiom set*. We now have that: zero for
  `atlas/`, `classic` and `functional_extensionality_dep` for DPL.
- **`REFUTED` needs real countermodels.** DPL's `negneg_witness` is a genuine
  machine-checked countermodel; a student should be shown it rather than told.

### The research output nobody else has

Log every turn of the loop: `{nl_claim, theory, draft, coqc_verdict, typed_error,
repair, final_bucket, n_attempts}`. That corpus — natural-language semantic
claims paired with compiler ground truth across twelve frameworks — is a
genuinely novel dataset, and it is generated as a by-product of students using
the tool. It is also the empirical backbone for paper §§4–5 (ROADMAP A5): *which
semantic phenomena are hard to formalize, measured by attempts-to-compile rather
than by opinion.* Ship it with a licence and a datasheet from day one; retrofit
consent is not possible.

### Guardrails

- The LLM never reports a verdict. `coqc`'s exit code does. The model's text is
  only ever an *explanation of* a verdict Coq already returned.
- Every explanation must cite a theorem name that exists in the corpus. If it
  cannot, it says so — a tutor that invents `Theorem donkey_anaphora_holds` is
  worse than no tutor.
- Cap repair attempts and surface the cap. "Failed after 3 attempts" is a
  finding; silently trying twenty and reporting the first success is not.
- Rate-limit and cache by statement hash — see `HOSTING.md`; the LLM is the
  budget line, not the hosting.

---

## The paper's experiments (ROADMAP A5, made concrete)

Three instruments, in dependency order. Together they are §§4-5's empirical
content; none exists in the current autoformalization literature in this form.

**E1. ATLAS-Bench.** Curate the loop logs into a versioned eval set:
`{nl_claim, theory, gold_bucket, gold_coq_statement}`. The four-bucket
structure is the novelty — no existing benchmark has NOT-STATABLE as a *gold
label*, and it is the label that requires a signature manifest to assign
honestly. Score submissions by compiler, not by string match: a candidate
statement is correct iff `coqc` proves it equivalent (`<->`) to the gold
statement, and mutation-generated near-misses (from L2's machinery) supply the
negatives. Licence and datasheet from day one; retrofit consent is impossible.

**E2. The typed-feedback ablation.** The loop section's central assertion —
typed feedback beats raw stderr — is currently an article of faith, and
`loop.py` ships the *control arm*. Run four arms over ATLAS-Bench: A0
independent resample (no feedback), A1 raw stderr tail (today's loop.py), A2
typed error only, A3 typed error + signature manifest. Deterministic gold
labels, fixed corpus, 12 rival object theories: an unusually clean setting,
and the extractor is needed for the tool regardless, so the experiment's
marginal cost is only the runs.

**E3. The 12×P formalizability matrix.** Take the union of phenomenon names
across `edges/*.json` (~25 unique), hand-author one canonical English claim
per phenomenon following GUIDE.md's sharpening protocol (the only manual
input, done once), and run the loop's best arm over all 12 theories. Output:
a complete machine-graded matrix — *which phenomena resist formalization,
measured in attempts-to-compile* — validated against the 7 hand-graded edges
as ground truth where they overlap. ≤ ~900 LLM calls (25 × 12 × ≤3 attempts;
NOT-STATABLE cells short-circuit on the signature check). This is the paper's
core table, and the thesis of the project made measurable.

## Educational additions (cheap, high leverage)

- **Predict-the-verdict.** Before the checker answers, the student commits to
  one of the four buckets. One extra click of vanilla JS; converts browsing
  into active prediction (the intervention learning science actually backs),
  and enriches every logged turn with *human prior vs compiler truth* — a
  misconception corpus per phenomenon per framework that nobody has.
- **Proof ladders.** DPL.v presents 171 theorems in compilation order, which
  is not learning order. Rank each theory's theorems by measured proof
  complexity — step count, max goal-state size, dependency depth, all from the
  step-7 artifacts — and render each theory page as a ladder from starter
  lemmas to headline results. Later: one-hole exercises (`Proof. ... ▢ ... Qed.`)
  generated from real proofs and prevalidated by `coqc` in CI, so no student
  ever meets an unsolvable exercise.
- **Countermodel exhibits.** Every REFUTED verdict has a machine-checked
  countermodel behind it (`negneg_witness` is the flagship). Render them as
  walkable exhibits — the model, the assignment, the failing clause — with
  every displayed value Coq-computed, not hand-copied into HTML.

## Citability (zero server cost)

- **Zenodo DOI per release**, wired to GitHub releases; release = the
  `claims.lock` changes (step 6), so a DOI names a specific set of statement
  hashes.
- **Per-theorem permalinks**: `#/theorem/<theory>/<name>` pinned to commit +
  statement hash, with a "cite this theorem" BibTeX button. The difference
  between being browsed and being cited.
- **One-command reproduction**: `make verify` reruns verify.py + coqchk and
  diffs against the committed `.mech.json` and `claims.lock` — a reviewer
  reproduces the whole evidentiary chain in one line.

---

## Notes for whoever picks this up

- `Print Assumptions` needs the **fully dotted** module path. `shallow/PTQ.v`
  and `atlas/montague/PTQ.v` both resolve to bare `PTQ`, and `Require Import
  PTQ` silently loads whichever the loadpath hits first — this cost an hour.
- Terminators are not line-anchored: `Proof. reflexivity. Qed.` is three
  commands on one line and is the dominant style in `PTQ.v`. Anchoring `Qed.`
  to `^` undercounts proved theorems by 3×.
- Term-mode proofs (`Theorem foo : T := e.`) have no `Qed` at all. They are
  counted via the `:=` check in `settle()`; anything else with no terminator is
  reported as `unparsed_status` rather than assumed proved.
- Never grep for axioms. `DPL.v:1950` contains "Axiom-free." inside a comment
  and a naive `/^\s*Axiom/` flags it. Comments are stripped and the real check
  goes through Coq.
- `verify.py` writes nothing into the Coq repo — `coqc -o` targets a temp dir,
  so a verification run cannot perturb the build.
