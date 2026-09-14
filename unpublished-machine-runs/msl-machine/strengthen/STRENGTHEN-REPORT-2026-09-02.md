# THE STRENGTHENER — Wang's loop, gated

`oracle/tools/msl_strengthen.py` (1,672 lines) · selftest **36/36 GREEN**, offline, $0
Receipts: `oracle/evidence/msl-machine/strengthen/`

> **The deliverable is the loop existing and being gated, not a pile of theorems.**
> Every number below is read off a kernel log or a `$0` deterministic gate.
> **VERIFIED_THEOREMs produced: 0.** Two targets were cut off by the box deletion and are
> marked NOT_RUN rather than guessed at.

---

## 1. What the organ is

Input: a **typed Lean statement `P` over one natural parameter** (a DAG node, or a fixture).
A cheap model proposes up to 4 **strengthened** statements `P'(n)` — each of which must
*imply* `P` — and deterministic gates plus the Lean kernel decide. The model holds no
authority: it cannot certify, cannot mark anything proved, and its prose is carried verbatim
and decides nothing.

```
   P (typed, over n : ℕ)
        │
        ├─ GATE E  equivalence     $0 syntactic  +  kernel `rfl` defeq probe
        ├─ GATE F  falsification   decide P'(0), P'(1), P'(2) on the box
        ├─ GATE T  binding         msl_obligation_dag.type_gate, IMPORTED
        │
        ├─ CHECK 1  ∀ n, P'(n) → P(n)          each its own .lean,
        ├─ CHECK 2  P'(0)                       autoImplicit false,
        ├─ CHECK 3  ∀ k, P'(k) → P'(k+1)        deterministic ladder first,
        │                                        then ONE proposer repair shot
        └─ COMPOSED FILE  ← the three lemmas + `induction` derivation of ∀ n, P n,
                            kernel-checked AS ONE UNIT with `#print axioms`.
                            VERIFIED_THEOREM is stamped off THIS and nothing else.
```

### Why it is not the decomposer

Decomposition goes **down**: a prose parent becomes typed children plus a composition
obligation. A strengthening goes **sideways then up**: it *implies* its target. That is the
opposite arrow — and `msl_decompose`'s GATE 3B (circularity) drops anything shaped
`<something> → <parent>` on sight. Neither organ can express the other.

### Reuse (nothing re-derived)

| Reused | From |
|---|---|
| ssh batch transport (`_ssh`, host, key, concurrency ceiling) | `msl_decompose.RemoteKernel` (subclassed) |
| `normalize_defs`, `normalize_type_spelling`, `ERROR_LINE`, `SORRY_WARN`, `AXIOM_LINE`, `CLEAN_AXIOMS`, `elaboration_verdict` | `msl_decompose` |
| **`type_gate`** (GATE T) and `norm_ws` | `msl_obligation_dag` — imported, not reimplemented |
| `LLMSpeaker` (the estate's one OpenRouter client) | `msl_machine` |
| `Budget` / `BudgetExhausted` / `PROPOSER_CALL_RESERVE_USD` / `PROPOSER_MODEL` | `msl_blade_forge` |

`run` is the only method overridden on the kernel, because the decomposer's remote
directories are module globals upstream and that file was outside my write scope. Mine lived
at `/root/peer/strengthen/`.

---

## 2. Three design decisions worth defending

**Heartbeats, not milliseconds.** The specified ladder is in ms (decide 50, omega 150, ring
100, linarith 200, nlinarith 500, gcongr 200, positivity 100, aesop 1000). A wall-clock cap
is not reproducible — it measures the box's load, and this box ran a shared decomposer sweep
at load 38. Each rung is emitted as `set_option maxHeartbeats <hb> in (<tac>; done)` with
`hb = ms × 20`, anchored so the 1000 ms rung lands exactly on the estate's existing
`msl_decompose.TRIVIAL_HEARTBEATS = 20000`. The ms figures survive as relative weights.

**The base is pinned at zero.** A declared base `b > 0` is **refused**
(`BASE_SHIFT_NOT_SUPPORTED`). Composing from a shifted base needs `Nat.le_induction`, and a
module that emits a `Nat.rec` composition while its base was proved at `b ≠ 0` emits an
unsound file. The proposer is instead told to encode the offset into `P'` itself
(`P'(n) := b ≤ n → …`). A refusal beats a composition the kernel happens not to catch.

**Three greens are not a theorem.** The three checks are re-emitted into one composed file
together with the final `induction` derivation, and *that* file's verdict is the receipt. The
composed file deliberately carries **no** goal-capture/`sorry` alternative, so a lemma that
closed in isolation and fails in context cannot fall through. Selftest scenario 5 exists to
prove the module behaves this way rather than merely claiming it.

---

## 3. Selftest — 36/36 GREEN, offline, $0, verified with no box

`python oracle/tools/msl_strengthen.py --selftest` — canned proposer **and** a scripted
kernel, so every gate, every verdict reader and the composition assembly run with no network,
no key and no Lean. Re-verified green locally after the box was taken out of the loop.

| Scenario | Assertion |
|---|---|
| S0a/S0b | shape refusals (`NOT_PARAMETRIC`, `PARAM_NOT_NAT`) before any spend |
| S1a–S1e | geometric-sum target, closed-form strengthening → `VERIFIED_THEOREM`, composed path, clean axioms, closing rung named, counts agree |
| S2/S2b/S2c | `P' = P` rejected by GATE E **and reached no kernel job** |
| S3 | `P'` false at n=1 dropped by GATE F |
| S4/S4b–S4e | type-dropping `P'` rejected by GATE T; relaxed bound recorded not hidden; standalone arm still bites untyped arithmetic |
| **S5–S5d** | **parts pass, composed file fails → NOT VERIFIED**, verified count 0, error banked |
| S6–S6i | emitted Lean well formed: `autoImplicit false`, no `sorry` in the composed file, axioms on the final theorem, every rung ends in `done`, rung reader not fooled by Lean's quoting |
| S7–S7e | verdict readers refuse the dangerous greens: sorry ⇒ OPEN, dirty axioms ⇒ OPEN, `sorryAx` ⇒ COMPOSITION_FAILED, GATE F silence ⇒ UNDECIDED, GATE E defeq success ⇒ REJECTION |
| **S8/S8b** | a repair call reserves the **measured** worst case; a second runaway is refused **before** the wire (see §7) |

---

## 4. What the $0 probe caught before any money moved

I ran the full pipeline against the real box with a **canned** proposer (zero spend) before
the live run. It found three real defects:

1. **The ladder accepted non-closing tactics.** `first` accepts any alternative that does not
   *throw*, and `simp`/`ring_nf` succeed by *making progress*. Observed: a check reporting
   `error: unsolved goals` **from inside the ladder**, the goal-capture alternative never
   running, and the repair shot therefore handed no goal state. A rung that "succeeds"
   without closing silently disables every rung after it. Fix: every rung is `(<tac>; done)`.
2. **The rung reader swallowed Lean's quoting** — `\S+` captured `t10_simp";` off Lean's own
   echo. Fix: a rung id is `[A-Za-z0-9_]+` and nothing else.
3. **GATE T rejected the highest-yield Wang move** — see §5.

Re-probed after the fixes: implication and base both `closed_by_t10_simp`, the step case
correctly OPEN **with the goal captured**. The machinery works end to end on real Lean, for $0.

---

## 5. The GATE T finding

Run naively with the target as reference, the imported `type_gate` **rejects the single
highest-yield Wang move**: replacing an inequality by its exact closed form necessarily drops
the inequality, and `type_gate`'s `DOMAIN_BOUND` regex reads the `i ≤ 2` inside
`∑ i ∈ range n, ((1:ℚ)/2)^i ≤ 2` as an inherited domain bound. That is the gate measuring the
*move*, not the mathematics.

The fix neither weakens nor reimplements the gate — it runs it in **two arms** and partitions
the gate's **own** `missing` vocabulary:

| Arm | Rule |
|---|---|
| **Standalone** `type_gate(P')` | untyped arithmetic in `P'` is **fatal**. The tuxedo proper. |
| **Referenced** `type_gate(P', P)` | missing **type** or **ascription** is **fatal** (dropping `(… : ℚ)` moves the statement to ℕ where `1/2 = 0`). |
| Referenced, domain bound only | **recorded** as a relaxation, not fatal. |

Why the relaxation is safe to record: a relaxed bound cannot put the statement over the wrong
type, and whether anything was actually lost is settled by **CHECK 1 — `∀ n, P'(n) → P(n)` —
in the kernel**. A kernel-checked implication is strictly stronger than a syntactic bound
comparison, and it is a check this organ already has to pass. The full referenced verdict is
banked verbatim, so a reader can disagree with the rule.

---

## 6. LIVE RUN — `erdos289`, 6 nodes

```
python oracle/tools/msl_strengthen.py --problem erdos289 \
       --budget-usd 0.50 --max-lean 8 --max-candidates 4 --max-repairs 3
```

**The DAG's own `manufacture_target` leaves are all prose.** Census of every
`dag/*.dag.json`: 207 nodes carry `manufacture_target: true`, and **205 are `MUST_DETERMINE`
plus 2 `BRANCH_STATEMENT` — zero typed Lean.** The typed population over a natural parameter
lives in the **decomposition sidecars** (`dag/decomp/erdos289/*.decomp.json`), whose children
are typed, kernel-elaborated statements awaiting ingest. Those are the live targets. Their
`manufacture_target` field is absent (not yet ingested), so the module **recomputes the
emitter's own rule** (`is_leaf ∧ binding ∈ {VERBATIM, PARAPHRASE} ∧ status ∈ {OPEN,
PROVED_SPEAKER}`) rather than asserting eligibility.

| # | node | param | outcome |
|---|---|---|---|
| 1 | `erdos289:A:M01#D1` | `n` | **RAN** — 4 candidates, all CHECKS_OPEN |
| 2 | `erdos289:A:M01#D2` | `n` | **RAN** — 4 candidates, all CHECKS_OPEN |
| 3 | `erdos289:A:M01#D3` | — | **REFUSED** `NOT_PARAMETRIC` (0 binders), $0 |
| 4 | `erdos289:B:M01#D1` | `k` | **NOT_RUN** — cut off mid-repair by box deletion |
| 5 | `erdos289:B:M01#D2` | `N` | **NOT_RUN** — never reached |
| 6 | `erdos289:P4:…-A-ROOT#D2` | — | **REFUSED** `NOT_PARAMETRIC` (0 binders), $0 |

### Target 1 — `2 ≤ n → ((1:ℚ)/n = (1:ℚ)/(n+1) + (1:ℚ)/(n*(n+1)))`

`{"proposed": 4, "dropped_gate_E": 0, "dropped_gate_F": 0, "dropped_gate_T": 0, "checks_open": 4, "composed_attempted": 0, "verified_theorems": 0, "repairs_used": 3}`

| # | kind | verdict | E | F | T | CHECK1 | CHECK2 | CHECK3 |
|---|---|---|---|---|---|---|---|---|
| S1 | closed_form | CHECKS_OPEN | PASS | PASS | PASS | OPEN | `t10_simp` | OPEN |
| S2 | extra_invariant | CHECKS_OPEN | PASS | PASS | PASS | OPEN | `t10_simp` | OPEN |
| S3 | generalized_hypothesis | CHECKS_OPEN | PASS | PASS | PASS | OPEN | `t10_simp` | OPEN |
| S4 | extra_invariant | CHECKS_OPEN | PASS | PASS | PASS | OPEN | `t10_simp` | OPEN |

- **S3** `(∀ m ≤ n, 2 ≤ m → (1:ℚ)/m = (1:ℚ)/(m+1) + (1:ℚ)/(m*(m+1)))` — the textbook
  strong-induction generalisation, proposed unprompted.
- **S2** conjoins `P(n)` with `P(n+1)` — the classic two-step invariant.
- Repairs: 3 fired, all `STILL_OPEN`; the remaining 5 open checks were `NOT_ATTEMPTED`
  (repair cap reached).

### Target 2 — `2 ≤ n → (n + 1) + 1 < n * (n + 1)`

`{"proposed": 4, "dropped_gate_E": 0, "dropped_gate_F": 0, "dropped_gate_T": 0, "checks_open": 4, "composed_attempted": 0, "verified_theorems": 0, "repairs_used": 3}`

| # | kind | verdict | E | F | T | CHECK1 | CHECK2 | CHECK3 |
|---|---|---|---|---|---|---|---|---|
| S1 | closed_form | CHECKS_OPEN | PASS | PASS | PASS | OPEN | `t10_simp` | OPEN |
| S2 | extra_invariant | CHECKS_OPEN | PASS | PASS | PASS | **`t10_simp`** | `t10_simp` | OPEN |
| S3 | generalized_hypothesis | CHECKS_OPEN | PASS | PASS | PASS | **`t10_simp`** | `t10_simp` | OPEN |
| S4 | generalized_hypothesis | CHECKS_OPEN | PASS | PASS | PASS | OPEN | `t10_simp` | OPEN |

- **S2** `(2 ≤ n) → ((n+2 : Nat) < n*(n+1) ∧ 4 ≤ n*n)` and **S3**
  `∀ m : Nat, m ≤ n → (2 ≤ m) → (m+2 : Nat) < m*(m+1)` each closed **two of three** checks —
  implication *and* base — leaving only the inductive step.

### Kernel-check tally over the two completed targets

**24 checks attempted (8 candidates × 3): CHECK 2 (base) closed 8/8, CHECK 1 (implication)
2/8, CHECK 3 (step) 0/8 — 10/24 closed.** No candidate closed all three, so **0 composed
files were attempted and 0 VERIFIED_THEOREMs were produced.** That is the honest result: the
bare ladder plus one repair shot does not close a research-grade inductive step, which is
exactly the outcome the gating is designed to report rather than paper over.

### Gate activity, live

Every one of the 8 candidates passed GATE E (syntactic **and** kernel `rfl` defeq), GATE F
(`decide` at 0/1/2 on the box) and GATE T. Nothing was dropped. The gates' teeth are
demonstrated by the **$0 probe**, where GATE F correctly killed a deliberately false `P'`
(false at 0, 1 **and** 2) on real Lean, and by the selftest, where each gate rejects its own
adversarial fixture.

---

## 7. Spend, and a real budget finding

**Total: $0.04461 over 11 proposer calls, cap $0.50 — 8.9% of budget.**

| call | USD | s | in | out |
|---|---|---|---|---|
| `t01.propose` | 0.00052 | 53 | 1133 | 1759 |
| `t01.c1.repair.implication` | 0.00017 | 5 | 571 | 167 |
| **`t01.c1.repair.step`** | **0.00408** | 174 | 577 | 7984 |
| `t01.c2.repair.implication` | 0.00006 | 3 | 621 | 62 |
| `t02.propose` | 0.00046 | 47 | 1112 | 1522 |
| `t02.c1.repair.implication` | 0.00023 | 24 | 524 | 744 |
| `t02.c1.repair.step` | 0.00012 | 10 | 530 | 319 |
| `t02.c2.repair.step` | 0.00049 | 62 | 527 | 1849 |
| `t04.propose` | 0.00200 | 246 | 1252 | 7638 |
| **`t04.c1.repair.step`** | **0.03282** | **1109** | 669 | **131072** |
| `t04.c2.repair.step` | 0.00366 | 92 | 666 | 7116 |

⛔ **One call was 74% of the entire run.** `t04.c1.repair.step` emitted **131,072 completion
tokens over 18.5 minutes** and cost **$0.03282** — **3.3× the shared
`PROPOSER_CALL_RESERVE_USD` of $0.01**, which `msl_blade_forge` documents as a *deliberate
over-estimate* precisely because "a budget that can be crossed is not a budget." For repair
shots that assumption is false: a repair prompt hands the model an open goal and asks for a
tactic block, and a model that starts enumerating does not stop. `LLMSpeaker` sends no
`max_tokens` and was not mine to change, so the defence available in scope is the **reserve**:
repair calls now charge `REPAIR_CALL_RESERVE_USD = 0.05`, the measured worst case. Over-
reserving is safe (`settle()` refunds the difference); under-reserving is how a cap silently
stops being a cap. Selftest S8/S8b lock this in.

This is worth carrying upstream: **any** estate module that fires repair-style prompts through
`LLMSpeaker` under the flat $0.01 reserve can cross its cap the same way.

---

## 8. Box evacuation (deletion directive)

- **Stopped**: no new kernel batches were launched after the directive. The final sweep
  confirmed **12 batches, unchanged** between the first and last pull — the in-flight target
  had not reached its next batch.
- **Pulled**: `/root/peer/strengthen/*` and `/root/peer/out/s2026*` → committed to
  `oracle/evidence/msl-machine/strengthen/box/` as both a tarball and an extracted tree.
  **325 files: 96 `.lean`, 108 `.log`**, every batch this organ ever ran, including the two
  `$0` probes.
- **Confirmed empty**: `find /root -maxdepth 3 -name '*strengthen*'` returns only
  `/root/peer/strengthen`, which is now mirrored locally. **Nothing I need remains on the box.**
- The composed/check `.lean` sources were always written locally *before* being sent, so
  `oracle/evidence/msl-machine/strengthen/erdos289/lean/` is independent of the box.
- **Selftest re-verified 36/36 GREEN locally with the box out of the loop.**

I did **not** force-kill the in-flight run: the repo's `blind_run_guard` blocks task kills and
requires the *user's* consent to destroy their compute, and a coordinator message is not user
consent. The run was idle in an HTTP call, everything was already evacuated, and the module
fails closed (`BOX_TIMEOUT` / `BOX_LAUNCH_FAILED`) if the box disappears — so no receipt can
be fabricated by the box vanishing.

**Final disposition (confirmed after the fact):** the run was terminated by the harness, not
by me, while still waiting on `t04.c3.repair.step`. That call never returned. The end state is
byte-for-byte what is reported above — **3 sidecars, 11 proposer receipts, $0.04461** — so the
NOT_RUN classification for targets 4 and 5 is final rather than provisional, and no partial
target-4 receipt exists to reconcile.

---

## 9. Honest bottom line

| | |
|---|---|
| Selftest | **36/36 GREEN**, offline, $0, no box |
| Targets attempted | 2 completed, 2 refused by shape ($0), **2 NOT_RUN** (box deletion) |
| Candidates gated | 8 (+2 in the $0 probe) |
| Gate rejections, live | 0 — all 8 passed E, F and T |
| Kernel checks closed | **10 / 24** (base 8/8, implication 2/8, step 0/8) |
| Composed files attempted | **0** |
| **VERIFIED_THEOREMs** | **0** |
| Spend | **$0.04461** of a $0.50 cap |

Zero theorems is the expected and correct outcome at this stage. What now exists that did not
before is the **organ**: a loop that proposes strengthenings, kills the false and the circular
ones deterministically, points a kernel at the three obligations that matter, and — critically
— **refuses to call anything proved until a single composed file carrying the whole derivation
comes back green with a clean axiom footprint.** The gates have been shown to bite on real
Lean (GATE F killed a false `P'`; the ladder's `done` defect was caught and fixed for $0), and
the module's own selftest proves it will not stamp VERIFIED when the parts pass and the whole
fails.

**Next move, when a box exists again:** the step case is the bottleneck (0/8). It needs the
repair shot to see Mathlib's `Finset.sum_range_succ`-style lemmas — i.e. a retrieval step in
the repair prompt, or a second repair shot budgeted at the now-measured reserve. Targets 4
and 5 (`erdos289:B:M01#D1/#D2`) are untouched and ready to re-run.
