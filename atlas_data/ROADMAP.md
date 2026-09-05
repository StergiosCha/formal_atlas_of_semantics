# FORMAL ATLAS — roadmap

State as of 2026-09-05. Two tracks run in parallel: **content** (more Coq, more
audited records) and **product** (the tool people actually open). The content
track is the moat; the product track is what makes it visible.

---

## Where we are

- 11 atlas Coq files, zero `Admitted`, zero propositional axioms outside DPL's
  documented classical/funext groups: `InqB`, `DPL`, `MTT`, `Ranta`,
  `MTT_vs_Ranta`, `DTS`, `PTQ`, `PTQ_vs_Lambek`, `PTQ_vs_MTT`, `RSA`, `DisCoCat`,
  plus the pre-atlas `Lambek`.
- 64 audit records; 7 comparison edges with per-phenomenon grades.
- 229 survey entries; ~101 still without a PDF on disk.
- `tool/` scaffold: Coq checker service + LLM draft-and-check loop + Docker.
- Zero verifier passes (`*.verify.json`) — the audit records are self-reported.

---

## Track A — content

**A1. `atlas/ttr/TTR.v`** (design ready, Cooper 2023 on disk)
Record types as the core, with the two hard bits: record subtyping as a
*computed* relation rather than a stipulated one, and the dependent record
fields that make TTR more than a feature structure. The payoff is the third
leg of the type-theory triangle: `MTT ↔ Ranta ↔ TTR`, which gives us a
family-internal similarity triangle nobody has published.

**A2. `atlas/dynamic/DRT_DPL.v`** (design ready)
Kamp's DRSs and the DPL relational semantics side by side, with the
translation theorem in the direction that actually holds and a countermodel
in the direction that doesn't. `DPL.v` already carries the accessibility
machinery, so this is a bridge file more than a new theory.

**A3. Verifier pass.** The single biggest credibility gap. Every record claims
`compiles: true` and a theorem count on its own authority. A verifier script
should, per file: run `coqc` clean, run `Print Assumptions` on every audited
theorem, count `Theorem|Lemma|Corollary` vs `Admitted|Axiom|Parameter`, and
emit `records/<name>.verify.json` with a pass/fail and the raw output. Then
the site shows a green check that means something. This is a day of work and
it converts the whole project from "trust me" to "check me".

**A4. Lambek → pregroup bridge** (CGS13). Closes the type-logical/categorical
gap and gives `lambek__discocat` real theorems instead of a hand-written edge.

**A5. Paper §§4–5.** The findings are already publishable and currently sit
only in commit messages: the G&S 1991 misprints, GF16's cost-sign outlier,
LG17 eq. (20) printing ~.015 where the formula gives 1/6486, and
`shallow/PTQ.v`'s `temperature_puzzle` being both `Admitted` and misformulated.

**A6. Collection.** 101 entries still without a file. `place_papers.py` now
handles the drop folder correctly — the bottleneck is acquisition through
legitimate channels (institutional proxy, ILL, author email). Bekki 2014 has
no open copy at all; a one-line email to Bekki would likely settle it, and
`DTS.v`'s determination stays `slight_modification` until it's checked.

---

## Track B — the tool

Four surfaces, in dependency order. Ship B1+B2 before touching B3.

**B1. The atlas view (landing).**
The edge graph rendered live from `atlas.json`: theories as plates, edges
weighted by similarity, thickness = mean joint grade, opacity = Jaccard
overlap. Click an edge → the per-phenomenon grade table with the actual Coq
theorem names. This is the hero image made interactive, and it is the thing
that will get shared.

**B2. Theory pages.**
One page per record, rendered from the JSON we already have: summary,
definitions-mapped table (Coq ↔ source ↔ match quality), theorem list with
status, the faithfulness verdict with its evidence/simplifications/omissions,
artifact classes, and — the differentiator — the `source_gap` field, which is
where we say out loud that a published paper has a misprint and prove it.

**B3. The proof reader.**
Coq source with a Proof-General-style locked region: processed prefix shaded
amber, current goal in a side pane, step forward/back. Two routes:
- **jsCoq** in the browser — no server, instant, but pinned to its own Coq
  version and slow to load a 1900-line file.
- **server-side `coqtop` session** behind the existing checker service —
  matches our actual toolchain, needs sandboxing and a session pool.
Recommendation: server-side, reusing `tool/`'s checker container, with a
per-session timeout and no filesystem write. It's the same security surface
we already accepted for B4.

**B4. The verifier (the educational hook).**
User types a claim in English → LLM drafts a Coq statement against a chosen
theory's file → the checker compiles it → the result lands in one of the four
GUIDE.md buckets: **PROVED**, **REFUTED** (with the countermodel), **NEEDS
ASSUMPTION** (with the assumption named), **NOT STATABLE** (with why the
theory's vocabulary can't express it). That fourth bucket is the pedagogically
valuable one and no existing tool has it.

**B5. Look and feel.** See `BRAND_PROMPT.md` — cartographic atlas plate, λ as
meridian, Proof General's locked-region amber as the accent, serif prose plus
a monospace with real Greek glyphs. The failure mode to avoid is dark-mode
neon "AI product"; the target is *Edward Tufte edits the Coq manual*.

---

## Track C — infrastructure

- **CI**: GitHub Actions running `make -k -j8` plus the A3 verifier on every
  push, with the badge on the README. Cheap, and it makes A3 self-maintaining.
- **README rewrite**: currently describes the pre-atlas repo.
- **Dedupe into `extras/attic/`**: the pre-atlas files (`kratzer2.v`,
  `BarwiseCooper.v`, `shallow/PTQ.v`) use `Parameter`s and are raw material,
  not atlas files. They should be visibly separated so nobody cites them as
  audited work.

---

## Suggested order

1. **A3 verifier** — unblocks the green checks the site needs, and audits what exists.
2. **B1 + B2** — the site becomes real using only data we already have.
3. **A1 TTR** — completes the type-theory triangle while the site is being built.
4. **C CI** — locks in A3.
5. **B3 proof reader**, then **B4 verifier UI**.
6. **A2 DRT**, **A4 Lambek→pregroup**, **A5 paper**.
