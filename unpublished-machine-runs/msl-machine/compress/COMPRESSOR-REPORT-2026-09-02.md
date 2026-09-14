# THE COMPRESSOR — `oracle/tools/msl_compress.py`

**Built 2026-09-02.** The organ that climbs. COMBINE / COMPRESS / RISE / LADDER.

> *"We mine the ore. At the same time the machine must be beautifully compressing the ore
> into gold. COMBINE. COMPRESS. RISE. LADDER. If that isn't happening as aggressively then
> we are shit in the water."*

---

## 1. THE PROBLEM, MEASURED BEFORE A LINE WAS WRITTEN

Read off the live estate the hour this module was built (226 DAGs + the door's ore, through
`msl_promote`'s own loaders):

| reading | value |
|---|---|
| union of kernel-proved statements | **373** (113 campaign + 260 door-only; 25 overlap) |
| problems holding proved work | 226 |
| problems with **≥ 2 proved statements that are a premise of nothing** | **72** |
| erdos479 | 26 proved, **23 of them premises of nothing** |
| erdos936 | 23 proved, **21 unused** |
| erdos289 | 21 proved, **16 unused** |

`msl_promote` (the sweeper) folds a parent only when its children **and** a **pre-written**
composition are *already* proved. It never proposes anything upward. So the pile grows and
nothing builds on it. That pile is not gold — it is smelted ore left on the floor.

---

## 2. WHAT WAS BUILT

`oracle/tools/msl_compress.py` — ~3,300 lines, `$0` by default, **116/116 selftest arms**,
offline, no box, no network, no Lean.

```bash
python oracle/tools/msl_compress.py --selftest                       # 116 arms, offline
python oracle/tools/msl_compress.py --problem erdos289 --harvest-only # $0, free gold only
python oracle/tools/msl_compress.py --problem erdos289 --budget-usd 0.50
python oracle/tools/msl_compress.py run --problem erdos289 --budget-usd 0.05   # box runner's form
python oracle/tools/msl_compress.py --report                          # re-render, runs nothing
```

### The stage order — and why each stage sits where it does

| # | stage | cost | why here |
|---|---|---|---|
| 0a | **HEADLINE LEDGER** | $0 | `NEAR_CLOSE` rows outrank every DAG open node |
| 0b | **ROOT-PULLED TARGETS** | $0 | a ladder climbs *toward* something |
| 0c | **FRONTIER-ADJACENT RUNGS** | $0 | added after the first live run proved root-pull alone is not enough (§5) |
| 1 | **CHAINS / DECOMP / DOOR HARVEST** | **$0** | not one cent is spent before the free gold is taken |
| 2 | **VOCABULARY GRAPH + LEVERAGE** | $0 | which 8 leaves go in the prompt is *computed*, never random |
| 3 | **DIRECTED INSTANTIATION LIFTS** | **$0** | the estate-wide fingerprint corpus, deterministic |
| 4 | **k-SAMPLE PROPOSER** | capped | k prompt variants per target; the kernel adjudicates all |
| 5 | **SEVEN GATES** | $0 | deterministic, fail-closed, first failure stops |
| 6 | **KERNEL JOBS** | $0 | two files per candidate in `msl_ladder`'s own shapes |
| 7 | **REGISTER + HAND OFF** | $0 | sidecar, standing lemma, strengthen handoff, lift row |
| 8 | **FIXED POINT** | — | height grows by *iteration*, and only when the pool actually grows |

### The seven gates

| gate | refuses |
|---|---|
| `G1_SCHEMA` | fields missing; a premise we did not offer (its source cannot be included) |
| `G2_TYPE` | **THE TUXEDO** — `msl_obligation_dag.type_gate`, both arms; a dropped ascription is fatal, a dropped domain bound is not (msl_strengthen's split) |
| `G3_CIRCULAR` | T restates a leaf — by text, by declaration, **and by fingerprint** (alpha-variants) |
| `G4_KILLED` | T restates a `KILLED_HEADLINE` → logged `KILLED_RESTATEMENT` |
| `G5_CONJUNCTION` | **T is the bare conjunction of its premises**, or is neither shorter than that conjunction nor a generalization of a bound/parameter |
| `G6_FALSIFY` | `decide` FALSE at 0/1/2 — `msl_strengthen.falsify_lean` reused verbatim; **silence is UNDECIDED, never a pass** |
| `G7_RISE` | never refuses — it *classifies*. RISE (discharges / matches / on the root path / named by the contract) vs **LATERAL**, which is kept, registered, and excluded from height and ratio |

### Honest height

- **Tower height** = longest chain leaf → T → T′ where **every level is RISE-qualified**.
- **Compression ratio** = RISE-proved statements at height ≥ 1 ÷ proved leaves.
- A LATERAL theorem cannot appear in either. Leaves are height 0, so *no proved T reads as
  height 0*, never 1.

---

## 3. THE HEADLINE LEDGER (`oracle/frontier_formalizer/HEADLINE-LEDGER.jsonl`)

**The file did not exist when this was written**, so the reader was coded to the declared
shape and its absence is a first-class, tested behaviour: it reads as *"the ledger was not
there"*, **never** as *"there are no paper-level results"*.

| row | rule | enforced by |
|---|---|---|
| `NEAR_CLOSE` **with** `remaining_obligation` | first-class TARGET, `depth_from_frontier: -1`, **ahead of every DAG open node**; the obligation TEXT is the target | `headline_targets` |
| `NEAR_CLOSE` **without** one | **refused as a target** — "nearly closed with nothing named as missing is a mood, not an obligation" | `headline_targets` |
| `KERNEL_VERIFIED` | usable LEAF with its `.lean` artifact as `source`, so the composed file includes it by source | `headline_leaves` |
| `KERNEL_VERIFIED` with no `.lean` | refused as a leaf — a proof we cannot include cannot enter a file checked from zero | `headline_leaves` |
| `KILLED_HEADLINE` / `status: KILLED` | NEGATIVE CONSTRAINT set, by fingerprint **and** content key | `killed_fingerprints` → `G4_KILLED` |

A row is a kill because its **declared** `class`/`status` field says so — never because the
text sounded negative. Unknown `class`/`status` values are kept and counted as unknown, not
dropped: silently discarding a vocabulary we were not told about is the exact failure the
ledger exists to end.

**Honest limit, recorded in the code:** `msl_promote.fingerprint` collapses ascribed binders
(`∀ (n : T),`) and does **not** collapse membership binders (`∀ n ∈ S,`). So an alpha
variant of the first shape is caught by fingerprint; either shape is caught verbatim by
content key. The selftest arms use the shape the fingerprinter actually recognises and the
limit is written down rather than papered over.

---

## 4. TWO REAL BUGS THE SELFTEST CAUGHT BEFORE ANY LIVE RUN

**(a) The conjunction gate was leaking — the one gate this organ cannot afford to leak.**
A campaign `KERNEL_DECL` node carries its whole declaration in `statement`
(`theorem fx_l1 : ∀ n ∈ Finset.Icc 2 4, n ≠ 5`); a proposer writes a bare proposition. The
gate compared one against the other, so a candidate that **was** the bare conjunction of its
three premises matched **0 of 3** conjuncts and sailed through. Fixed by `_proposition_of()`
(strips a `theorem <name> <binders> :` head at bracket depth zero, drops a `:= …` tail),
now used by the conjunction gate, the circularity gate, the generalization measure and the
composed-file builder alike.

**(b) A job file was being offered as a kernel receipt.** The first implementation handed
`DagBuilder.add` a `PROVED_KERNEL` node whose `receipt` was our own `<T>.jobs.json` — a file
of *demands*. `_gate_kernel_receipt` refused it, exactly as it should. Fixed by
`bank_receipt()`, which writes the three files the estate's loaders already read
(`.lean` / `.verify.json` / `.axioms.txt`) in `msl_ladder.write_receipt`'s shape, with the
sha256 the emitter re-checks on every later emission. Arms 106–109 keep both halves alive,
including a tamper arm: a `.lean` edited after banking stops matching its pinned sha.

Writing into another organ's store is **off by default** (`bank_to_campaign=False`); the
ladder's own `--fire` path banks to the campaign when the box returns.

---

## 5. WHAT THE FIRST LIVE RUN CHANGED

Root-pulling on the three biggest problems returned **exactly one target each**, and in all
three it was the whole affirmative `BRANCH_STATEMENT`:

> erdos289 — *"AFFIRMATIVE: prove for all k ≥ K0 … a valid k-interval decomposition of 1
> exists"*

That is a correct root-path target (`ROOT → BRANCH_A → a proved leaf`) and **useless as the
only one**: handing a proposer eight lemmas and "now close the branch" asks for the problem,
not for a rung. *A ladder whose only visible rung is the top of the ladder has no rungs.*

`frontier_adjacent_targets()` was added: OPEN nodes **directly above** proved work, ordered
by how much proved work already points at them, labelled `on_root_path: false` so a rung is
never confused with a summit.

| problem | targets before | targets after |
|---|---|---|
| erdos289 | 1 | **8** |
| erdos479 | 1 | **5** |
| erdos936 | 1 | **2** |

---

## 6. THE BOX-RUNNER CONTRACT

`msl_box_runner.py`'s compression law reads `compress/COMPRESSION-<date>.json` for the
height it enforces on. Its reader (`Compressor.metrics`, read-only, never edited) walks
`doc["problems"]` as a **dict of problem → row**.

**The first live file got this wrong:** `problems` was a list of slug *strings*, so the
runner's `isinstance(r, dict)` filter dropped every row and both numbers came back `null` —
the lane was reading a real file and learning nothing from it. `metrics_document()` now
emits:

- top-level **`max_tower_height`** and **`max_compression_ratio`** (explicit, not derived);
- **`problems`** as the dict of rows carrying `tower_height` / `compression_ratio`;
- the run list moved to `problems_run`.

The estate ratio is deliberately **not** a mean of per-problem ratios — it is
(RISE statements at height ≥ 1) ÷ (proved leaves) summed across the run, so a 2-leaf problem
does not weigh as much as a 26-leaf one.

Arms **112–116** import the runner and drive **its own reader** over a file this module
wrote: non-null height, non-null ratio, one normalized row per problem, and — the arm that
matters most tonight — a run that proved nothing reads back as **height 0.0, not absent**,
so the runner is free to call it a stall.

---

Confirmed by running the runner's `plan` itself — `python oracle/tools/msl_box_runner.py
plan --cores 29`, lines 7–29 of its output:

```json
"compressor_lane": {
  "cores": 4,
  "available": true,
  "reason": "available",
  "metrics": {
    "max_tower_height": 0.0,
    "max_compression_ratio": 0.0,
    "problems": {
      "erdos289": {"tower_height": 0.0, "compression_ratio": 0.0},
      "erdos479": {"tower_height": 0.0, "compression_ratio": 0.0},
      "erdos936": {"tower_height": 0.0, "compression_ratio": 0.0}
    },
    "path": "oracle/evidence/msl-machine/compress/COMPRESSION-2026-09-02.json"
  }
}
```

**Non-null, read from this module's file, three rows parsed.** It was `null` before.

---

## 8. THE THIRD BUG — FOUND BY THE FIRST PAID RUN, AND THE MOST EXPENSIVE ONE

First paid run: 24 calls, $0.0139, 24 candidates, and **only 16 kernel jobs filed** — 15 of
24 candidates cleared **all seven gates** and then died at job-build:

```
NO_INCLUDABLE_SOURCE for premise erdos479:LEM:R009:L1: no source file, no typed
statement line, no theorem-shaped statement -- refusing to compose a file that cannot
be checked from zero
```

The cause is a real property of the estate, not a proposer failure:

> **A `LEM:*` node can be `PROVED_KERNEL` and still be PROSE.**
>
> `erdos289:LEM:R008:F1` — *"Any admissible decomposition of 1 containing 2 has the run
> containing 2 equal to exactly [2,3] … KERNEL_CHECKED: F1_head_forced, F1_tail_value."*

That node is proved, and it names the two declarations that prove it — but it carries no
`.lean`, no `lean_statement_line`, no theorem-shaped statement. It is a **summary** of kernel
work, and a summary cannot be included by source. Offering one as a premise buys a call that
can never become a file.

`includable()` now filters the premise pool **before the prompt**, using the *same function*
that would later build the file. The prose-proved leaves are counted and reported.

| problem | offerable premises | proved-but-PROSE |
|---|---|---|
| erdos289 | 14 | 2 |
| erdos479 | **6** | **17** |
| erdos936 | **4** | **17** |
| **total** | **24** | **36** |

**36 of the 60 unused proved leaves on these three problems are proved in name only.** That
is a first-class estate finding in its own right: the fix for those is **formalization, not
compression**, and the compressor now says so instead of burning calls on them.

Effect, same three problems, same budget shape:

| | run 1 | run 2 (filtered pool) |
|---|---|---|
| model candidates | 24 | 24 |
| **kernel jobs filed** | **16** | **46** |
| erdos479 jobs | **0** | **16** |
| erdos936 jobs | **0** | **12** |
| gated/refused | 1 `G2_TYPE` + **15 `JOB_BUILD`** | 1 `G1_SCHEMA` |
| spend | $0.0139 | $0.0182 |

---

## 9. RESULTS — LIVE, OFFLINE, 2026-09-02

**Disclosed before the wire:** model `z-ai/glm-5.3-flash`, cap **$0.50**, upper bound 27
calls (3 problems × 3 targets × k=3 × 1 round). **Actual: 24 calls, $0.018237.**

| problem | proved leaves | unused | targets | free chains | free decomp | lifts | model | **jobs filed** | proved T | lateral | height | ratio | dist |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| erdos289 | 21 | 16 | **8** | 0 | 0 | 0 | 9 | **18** | 0 | 1 | 0 | 0.0 | 2→2 |
| erdos479 | 26 | 23 | **5** | 0 | 0 | 0 | 9 | **16** | 0 | 1 | 0 | 0.0 | 2→2 |
| erdos936 | 23 | 21 | **2** | 0 | 0 | 0 | 6 | **12** | 0 | 0 | 0 | 0.0 | 2→2 |
| **total** | **70** | **60** | 15 | **0** | **0** | **0** | **24** | **46** | **0** | 2 | **0** | **0.0** | — |

**23 of 24 candidates cleared all seven gates** (one refused at `G1_SCHEMA`), each with two
kernel job files: the implication by source inclusion and T standalone. A sample:

| problem | T | rise | statement |
|---|---|---|---|
| erdos289 | `W4_two_interval_fragment` | RISE | `∀ a ∈ Finset.Icc 5 60, ∀ b ∈ Finset.Icc (a+1) …` |
| erdos289 | `erdos289_bridge_head_tail` | RISE | `((∃ (m : ℕ) (as bs : Fin m → ℕ), …` |
| erdos479 | `erdos479_k_neg_one_inf` | RISE | `(N : ℕ) : ∃ n : ℕ, N ≤ n ∧ (2:ℤ)^n ≡ -1 [ZMOD …]` |
| erdos479 | `erdos479_k3_no_witness_range` | RISE | `∀ n ∈ Finset.Icc (1:ℕ) 120, (2^n : ℕ) …` |
| erdos936 | `erdos936_81_dvd_iff` | RISE | `(n : ℕ) : 81 ∣ 2^n + 1 ↔ n % 54 = 27` |
| erdos936 | `erdos936_three_adic_lifting` | RISE | `(n k : ℕ) : (3^(k+1) : ℕ) ∣ 2^n + …` |
| erdos936 | `erdos936_odd_not_mult3_not_powerful` | **LATERAL** | kept, registered, **excluded from height** |

### The zeros, and why each is honest

- **`proved_T` 0, `height` 0, `ratio` 0.0** — there is no Lean on this machine. 46 jobs are
  filed; not one claims a thing. This is the expected and correct reading, and the box runner
  is free to call it a stall.
- **`free chains` 0** — 301 chains were read across the three problems (erdos289 27,
  erdos479 136, erdos936 138) and **all 301 had at least one premise that joins no proved
  statement**. That is not a wiring gap; the chain corpus says so in its own
  `ingest_contract`: its nodes are mined PROSE at `binding: PARAPHRASE`. The harvest ran, the
  join used the sweeper's own proved keys, and the count is the finding.
- **`free decomp` 0** — 9 decomposer sidecars across the three problems, **0 with all
  children proved** (3 each with children still open on erdos289 and erdos936).
- **`lifts` 0** — erdos289/erdos479 branch targets were liftable and matched nothing above
  0.55 Jaccard among 389 fingerprints; erdos936's was refused as prose
  (`NO_RELATION: no quantifier or relational symbol`).

---

## 10. WHAT IS ON DISK

```
oracle/tools/msl_compress.py                          the organ (118/118 arms)
oracle/evidence/msl-machine/compress/
  COMPRESSION-2026-09-02.md                           the operator's dashboard
  COMPRESSION-2026-09-02.json                         the box runner's contract
  <problem>/<T_id>.compress.json                      one sidecar per candidate
  <problem>/jobs/<T>.implication.lean                 source-inclusion composed file
  <problem>/jobs/<T>.standalone.lean                  T under the deterministic ladder
  <problem>/jobs/<T>.jobs.json                        both jobs + cable spec + source shas
  <problem>/STANDING-LEMMAS.json                      msl_campaign's packet shape
  <problem>/lift-corpus-additions.json                offered only at PROVED_KERNEL
  <problem>/strengthen-handoff/*.decomp.json          msl_strengthen.load_targets reads these
  _receipts/2026-09-02/*.proposer.json|txt            every call, its hash and its cost
```

**Nothing outside `oracle/tools/msl_compress.py` and `oracle/evidence/msl-machine/compress/`
was written.** No sibling MSL module was edited; all are imported.

---

## 11. THE ONE THING TO DO NEXT

The 46 filed jobs are in `msl_ladder`'s shapes and carry a validated `msl_lean_cable` spec,
so **they flow to the box with no new consumer**. When Lean is available:

```bash
# the jobs are already written; the box runner's compressor lane picks them up
python oracle/tools/msl_box_runner.py run --cores 29 --fire
```

The first clean verdict on an implication file is the first time this estate's tower height
is not zero.

