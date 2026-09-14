# DECOMPOSITION SWEEP — FINAL REPORT

**FINAL. The box was deleted at 17:06 UTC**; the sweep ran 16:22 -> 17:06 (44 minutes) and
died with it, mid-problem, exactly as expected. Everything box-only was evacuated first
(twice: 16:49 and 16:56). Totals below are the closing state, read off the sidecars on
disk by `python MINE/tally.py`, which re-derives them at any time. What the deletion
prevented is listed as **NOT_RUN**, never estimated.

---

## 0. HEADLINE

| the deliverable | count |
|---|---|
| **NEW FORMAL LEAVES estate-wide** (typed Lean, elaborated + bound + non-circular + non-trivial) | **111** |
| **of which FORMAL DECIDABLE** (carry a decidable tactic hint — the rung loop can fire on these) | **39** |
| **COMPOSITIONS KERNEL_CHECKED** (the count that actually advances a parent) | **11** |
| children thereby counting toward their parent | **33** |
| USD spent on the proposer | **$0.2563** of the $3.00 cap (8.5% — the cap never bound) |
| problems touched / prose nodes attempted | 45 / 109 (14 proposer refusals) |

Before this run the estate had **5** decomposition sidecars and **0** kernel-checked
compositions. A surviving child under an OPEN composition contributes **zero** to its
parent; it is still a formal leaf for the rung loop, and the two numbers are kept apart
everywhere.

---

## 1. `--all-prose` was accepted and ignored — now it walks the estate

`main()` parsed the flag, then **required `--problem`/`--dag` and walked exactly one DAG**.
A flag that names a sweep and performs one problem is worse than a missing flag: the
operator reads the help text and believes the estate was covered.

| | |
|---|---|
| DAGs on disk in the ranking | **225** |
| skipped as REFUSED by the census | 1 (`erdos850`, `NO_FROZEN_CONTRACT` — its file exists, which is why "on disk" is not the test) |
| eligible OPEN prose obligations | **542** (`LEMMA` 240 · `MUST_DETERMINE` 202 · `CAPABILITY_DEMAND` 100) |
| selected | **535** across **173** problems |
| **completed before the box died** | **109 nodes across 45 problems** |
| **NOT_RUN (box deleted)** | **426 nodes across ~128 problems** |

Order is **read, not re-derived** — `INDEX.json.ranking_by_closability`, the emitter's own
census. A DAG on disk the ranking never mentions is *appended*, never silently dropped.
The walk is **resumable**: a node whose sidecar exists is not re-proposed, so the remaining
nodes can be picked up on a new box with the same command and no repeat spend.

New flags: `--per-problem`, `--redo`, `--parallel-problems`, `--propose-workers`,
`--reverse` (a second worker on the same ranking from its other end), `--no-mirror`.

## 2. THE CONSUMER BUG — found, fixed at the source, and MEASURED

The rung loop reported erdos289 coming back **0/6**. Cause: `/root/leaf_prove.py:28`
rebuilds each leaf file itself instead of compiling what the kernel compiled:

```python
src = "import Mathlib\nopen Finset BigOperators Nat\nset_option maxHeartbeats 800000\n\n" \
      + (defs or "") + "\n\ntheorem leaf_%s :\n  %s := %s\n" % (sanitize(tag), stmt, proof)
```

Four defects, in order of damage:

1. **It drops `lean_binders`.** 4 of the 6 erdos289 children carry one (`(n : Nat)`,
   `(k : Nat)`, `(N : Nat)`). The consumer emits `theorem leaf_x : <statement>`.
2. **No `set_option autoImplicit false`.** With autoImplicit at its default *on*, the freed
   variable is silently auto-bound as an implicit — so those leaves are proof-searched
   **against a different statement from the one the kernel elaborated**. This is exactly
   the failure the decomposer's `autoImplicit false` law exists to prevent, reintroduced
   one process downstream.
3. **`open Nat`.** Measured on this box the same hour: `gcd a b` →
   `error: Ambiguous term gcd` (`Nat.gcd` vs `GCDMonoid.gcd`), which kills number-theoretic
   statements — most of this frontier. The decomposer deliberately does **not** open `Nat`;
   a proposal needing a namespace writes its own `open`, which `normalize_defs` hoists.
4. No `maxRecDepth`, and the *raw* definitions block rather than the normalised one.

**Fix.** `lean_statement_file` is now literally `lean_preamble(...) + lean_theorem_line(...)`,
so one string is both what the kernel compiled and what the sidecar ships. Every child and
composition node carries `lean_preamble`, `lean_signature`
(`theorem <name> <binders> : <stmt>` — **the binders live here**), `lean_statement_line`,
`lean_trailer` (composition: the `#print axioms` line), `lean_file_sha256`, and a
`lean_file_contract` telling the consumer how to compile it for elaboration *and* for a
proof attempt. The emitter **refuses to write a sidecar** (`PREAMBLE_DIVERGENCE`) if the
concatenation is not byte-identical to what the kernel was handed.

**Measured, not asserted.** The 9 pre-existing erdos289 nodes were backfilled — header read
back off the compiled `.lean`, **never re-synthesised**, because those files were compiled
under `open Finset` alone and stamping today's header on yesterday's verdict would be a
claim about a file that was never run — then rebuilt *from the sidecar fields alone* and
sent to the kernel:

```
CONSUMER-EQUIVALENT ELABORATION: 6/9
  erdos289:A:M01#D1 / #D2 / #D3   ELABORATES     erdos289:B:M01#D1 / #D2   ELABORATES
  erdos289:P4:...-A-ROOT#D2       ELABORATES     3 x #COMPOSE  unsolved goals (legitimately OPEN)
```

**6 of 6 leaves now elaborate. It was 0/6.** Audit across every emitted node:
**45 Lean-carrying nodes, 45 self-contained and sha-verified, 0 defects** (20 further
composition nodes were never constructed — no surviving child to compose).

### 2b. ⛔ THE CONSUMER WAS NOT FIXED, AND ITS 15 "PROVED" ROWS MUST NOT BE BANKED

Rescued from the box: 32 `LEAF-RESULTS.json` written by the peer's own rung loop against my
sidecars — **125 attempts, 15 marked `proved` with clean axiom footprints.** That looks like
a win. It is not bankable, and this is the most important line in this report.

`/root/leaf_prove.py` (mtime 16:24, *after* my sweep began) is **unchanged**: still no
`lean_preamble`, no `lean_signature`, no `autoImplicit false`. So those 15 rows were
compiled under the broken header. Checked against the sidecars:

```
peer-PROVED nodes: 15 | carry binders the consumer DROPPED: 5 | no binders: 10
  erdos124:LEM:R007:L1#COMPOSE                ['(r : ℕ)', '(d : Fin r → ℕ)']
  erdos289:A:M01#D1                           ['(n : Nat)']
  erdos289:A:M01#D2                           ['(n : Nat)']
  erdos400:LEM:R008:L1_g2_small_range#COMPOSE ['(n : Nat)']
  erdos936:DEMAND:R020:L1:1#COMPOSE           ['(k : Nat)']
```

**Those 5 are proofs of a different theorem** — the binder was dropped and auto-bound as an
implicit. 13 of the 15 closed on `by intros; aesop`, which is the shape an over-generalised
or vacuous restatement produces. The remaining 10 carry no binders but were still compiled
without `autoImplicit false` and with `open Nat`, so they are **not reproducible under the
decomposer's contract** without a re-check. **None of the 15 are counted anywhere in this
report's totals.** The 8 KERNEL_CHECKED compositions in §0 are GATE 4's own verdicts, run by
this module on the file it emitted.

> **ACTION REQUIRED (outside my write scope).** `/root/leaf_prove.py:28` →
> `src = node["lean_preamble"] + node["lean_signature"] + " := " + proof + "\n" + node.get("lean_trailer","")`
> Then re-run those 125 attempts. Until then the sidecars are correct and the consumer is not.

## 3. Selftest: 50 → 78 arms, all green

50-59 the multi-DAG walk (order read; unranked appended; REFUSED skipped *with a file on
disk*; ABSENT skipped; `--limit`; resumability both ways) · 60-65 the sweep (multi-problem,
per-problem dirs, totals, **clean stop at a shared cap with post-stop problems marked, not
dropped**) · 66 the `-P` clamp · **67-72 the preamble law, including the demanded arm — a
child whose preamble lacks the open it needs FAILS gate 1** (the kernel stub judges the
actual text it is handed, so it cannot pass a file it never saw) and passes once the open is
restored · 73-75 the signature keeps its binders · 76 **parallel problems + parallel
proposer calls give byte-identical totals to serial** · 77 `--reverse` is the same plan,
reversed.

## 4. Box batching (item 2) — existed already; ceiling raised

`RemoteKernel.run` already shipped a batch over one ssh, wrote a `nohup` runner with
`xargs -P`, kept per-file `.log`/`.rc`, polled for `DONE` and pulled results back. **No
reinvention was needed.** It was hard-capped at `-P4`; raised to a **ceiling of 16** per the
go-order, clamped to `[1,16]`, with the real total printed at launch. Measured: the box was
**not** the bottleneck (a 21-job batch ran 19/21 in 20 s; oleans warm) — the proposer was
(29 s–166 s/call), so concurrency was added there too.

## 5. Item 4 — the deterministic ladder on COMPOSITION nodes

GATE 4 swung the ladder (`tauto`, `intro h; exact h.1`, `simp_all`, `omega`, `norm_num`,
`aesop`, `decide`; 400 000 heartbeats ≈ the 60 s cap) at **every composition constructed**:
**95 emitted, 11 KERNEL_CHECKED** with footprints inside
`{propext, Classical.choice, Quot.sound}`. The 3 pre-existing erdos289 compositions were
re-swung during the reconstruction check: **0/3 close** (`unsolved goals` — real mathematics,
not a header failure).

**NOT_RUN:** the planned end-of-run retry pass over all remaining OPEN compositions
(`MINE/retry_compositions.py`, written and ready) never ran — the coordinator's stop order
forbade new elaboration batches. It is a $0 re-swing on a new box.

## 6. Per-problem results (45 problems, 109 nodes — closing state)

```
problem          node  prop  elab  bind  ncrc  ntrv  surv compK  fire
erdos1085           5    19    15    13    13    13    13     0    11
erdos507            4    13     9     9     9     9     9     2     0
erdos1108           4    14    11    11    11     8     8     2     0
erdos289            5    11     8     8     8     6     6     0     4
erdos936            4    13     6     6     6     6     6     1     0
erdos1101           6    19    11     9     9     5     5     2     0
erdos1104           3     7     5     5     5     5     5     1     1
erdos288            3     7     7     5     5     5     5     0     3
erdos680            2     4     4     4     4     4     4     0     0
erdos887            3    10     4     4     4     4     4     0     1
erdos931            3     6     4     4     4     4     4     0     0
erdos938            3    10     4     4     4     4     4     0     0
erdos1052           2     6     6     6     6     3     3     0     3
erdos1060           1     3     3     3     3     3     3     1     2
erdos1065           1     3     3     3     3     3     3     0     3
erdos1113           5    17     7     5     5     3     3     0     3
erdos1145           2     6     3     3     3     3     3     0     3
erdos124            2     3     3     3     3     3     3     0     3
erdos18             2     7     7     7     7     3     3     0     1
erdos400            3     8     5     3     3     3     3     1     0
erdos421            2     8     3     3     3     3     3     1     0
erdos212            1     2     2     2     2     2     2     0     0
erdos324            1     2     2     2     2     2     2     0     0
erdos340            4    15     3     3     3     2     2     0     0
erdos470            2     2     2     2     2     2     2     0     0
erdos306            3    11     3     3     3     1     1     0     0
erdos830            5    11     3     3     2     1     1     0     0
erdos9              2     2     1     1     1     1     1     0     1

erdos1056 erdos1106 erdos137 erdos168 erdos188 erdos208 erdos28 erdos389
erdos40 erdos424 erdos456 erdos508 erdos600 erdos786 erdos853 erdos950
erdos968
                                                 ... all 0 surviving
TOTAL             109   298   153   138   137   111   111    11    39
```

Gate attrition, honestly: 298 proposed → 153 elaborate (GATE 1 rejects 49%) → 138 bind
(GATE 2 tuxedo law drops 15) → 137 non-circular (GATE 3B drops 1 modus-ponens child) → 111
non-trivial (GATE 3 drops 26 as padding). **37% of what the model proposed survived**, and
the 187 rejections each carry the kernel's own error text in the sidecar. The
gates are doing the work they exist to do.

## 7. Box evacuation — CONFIRMED COMPLETE

| pulled | to `MINE/box-rescue/` |
|---|---|
| `/root/peer/dag` (sidecars **+ 32 `LEAF-RESULTS.json`, box-only**) | `peer-dag-final.tar.gz`, refreshed as `peer-refresh-1656.tar.gz` |
| `/root/peer/decomp` (560 `.lean` + every batch `run.sh`) | `peer-decomp-and-dagdecomp.tar.gz` |
| `/root/peer/out` (1 479 kernel logs + `.rc`, 1.1 MB) | `peer-out.tar.gz` |
| `/root/leaf_prove.py`, `leaf_prove_model.py`, `ladder_rung.py`, `sweep_daemon.py` | `peer-consumer-scripts.tar.gz` |

All four extracted and verified: **4 420 files, 12 MB**, in `MINE/box-rescue/x/`.
**Deliberately left:** `/root/peer/out/hh27720.drat`, 5.9 GB — another session's SAT proof,
not this task's and not mine to move.

**Local is primary and complete: 109 sidecars**, every one written locally first. The last
box comparison (16:56) was 92 = 92; the 17 written after it were mirrored as they landed
and are local regardless — the mirror is a copy for the peer, never the original, every one
mirrored and **sha256-verified off the box** as it landed. **Nothing I need remains on the
box.**

One note: the sweep process could not be killed — `blind_run_guard.py` refuses `TaskStop`
("did you ASK THE USER before destroying their compute?"). I did **not** route around it. It
holds no unflushed state; every completed problem's sidecar was written and mirrored before
the next began, and the process will terminate itself when the box disappears.

## 8. To resume on a new box

```bash
python oracle/tools/msl_decompose.py --selftest        # 78/78, offline, $0
python oracle/tools/msl_decompose.py --all-prose --budget-usd 2.85 \
       --max-lean 2 --parallel-problems 8 --propose-workers 3
```

Resumes at the untouched nodes (sidecars already written are skipped, no repeat spend),
after `BOX_HOST`/`BOX_KEY` are pointed at the replacement. Then the $0 re-swing:
`python MINE/retry_compositions.py --max-lean 8`.
