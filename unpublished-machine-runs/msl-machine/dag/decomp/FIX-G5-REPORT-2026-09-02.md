# FIXER — HUNT 3 / G5: the composition captured child binders by NAME

**2026-09-02.** Counter-agent to HUNT 3 finding **G5 (HIGH)**, `oracle/tools/msl_decompose.py`.
$0. No model call, no Lean, no fleet, no git. Writes confined to the declared scope:
`oracle/tools/msl_decompose.py`, the two live sidecars under
`oracle/evidence/msl-machine/dag/decomp/`, and this scratchpad.

**Selftest: 108/108 → 113/113.** Every original arm still green; five new arms added.
**Live captures: 2 → 0.** Both re-emitted, neither deleted.

---

## THE DEFECT, IN ONE LINE

`composition_conjunct` decided whether a child "shares the parent's binder" with

```python
extra = [b for b in child["binders"]
         if not set(_binder_names([b])) <= set(parent_binder_names)]
```

— a comparison over **names**. A binder's TYPE was never compared, and for a hypothesis
binder its PROPOSITION was never compared. So a child binder whose *name* the parent
carried was **dropped**, and the child's variable was re-bound at the parent's binder.

Two live consequences, both banked as `COMPOSITION_OPEN` — a **mathematical** outcome —
for what is an **emitter** defect:

| node | child binder | parent binder | what the file said |
|---|---|---|---|
| `erdos1085:B:M01#D6` | `(hd : 4 ≤ d)` | `(hd : 1 ≤ d)` | the child asserted under a hypothesis it was never proved under |
| `erdos124:LEM:R007:L1#D1` | `(d : ℕ)` | `(d : Fin r → ℕ)` | `d` re-bound as a FUNCTION; kernel: `Application type mismatch` ×2 |

The dangerous one is the first: a hypothesis **weakened** from `4 ≤ d` to `1 ≤ d` can close
for ordinary arithmetic reasons, and the parent is then licensed by a child that does not
supply the hypothesis.

---

## PROBE, BEFORE

`hunt3/probe04_composition_binder_capture.py` and `probe04b_live_capture.py`, verbatim
(`BEFORE-probe04.log`, `BEFORE-probe04b.log`):

```
  SAME NAME, DIFFERENT TYPE          parent['(n : ℕ)'] child['(n : ℚ)']
      conjunct emitted -> (n / 2 + n / 2 = n)
      child's own binder survived? NO -- DROPPED, name captured by the parent
  SAME NAME, DIFFERENT TYPE (Fin)    parent['(k : ℕ)'] child['(k : Fin 5)']
      conjunct emitted -> (k.val < 5)
      child's own binder survived? NO -- DROPPED, name captured by the parent

  the composition states:
      theorem msl_comp_probe (n : ℕ) : ((n / 2 + n / 2 = n)) → (2 * n = n + n)

  decomp sidecars on disk: 109
  COMPOSITION nodes: 95   children scanned: 111
  child binders captured by name with a DIFFERENT binder string: 2
     parent=['(d : Nat)', '(n : Nat)', '(hd : 1 ≤ d)', '(hn : 2 ≤ n)'] child_binder='(hd : 4 ≤ d)'
     parent=['(r : ℕ)', '(d : Fin r → ℕ)'] child_binder='(d : ℕ)'
```

Baseline selftest, before any edit (`BEFORE-selftest.log`): **108/108 checks pass**.

---

## THE FIX

`oracle/tools/msl_decompose.py`, three edits and one signature change.

### 1. `composition_conjunct` compares BINDERS, not names

The parent side is now the parent's **binder strings**, not `_binder_names(...)` of them —
a name without its type is exactly what G5 was, so the old argument no longer exists.
Three outcomes per child binder, and there is no fourth:

| outcome | test | emission |
|---|---|---|
| **SHARED** | identical to a parent binder (modulo whitespace and `Nat`≡`ℕ` only) | stays FREE — dropped from the conjunct, as documented |
| **EXTRA** | a name the parent does not carry | universally closed INSIDE the conjunct |
| **COLLISION** | same name, different binder | see below |

A **COLLISION** on a *hypothesis* binder (type contains a relation symbol) is carried as an
**explicit premise**: the binder is universally closed inside the conjunct and the node is
flagged `COMPOSITION_EXTRA_HYPOTHESIS`. The implication stated is then
`children ∧ extra_hyps → parent` — **honestly weaker** than `children → parent`, and never
the child asserted under the parent's weaker hypothesis.

A **COLLISION** on anything else raises `CompositionBinderMismatch`
(`COMPOSITION_BINDER_MISMATCH`), naming **both types**. Refusal rather than re-binding,
because both alternatives are wrong: dropping re-types the child (the erdos124 capture),
and universal closure would shadow the parent's own binder so the same identifier would
mean two things in one theorem and no consumer of `lean_signature` could tell which.

The hypothesis test is **fail-closed on purpose**. `→` is excluded from the relation set —
it is the function arrow in `Fin r → ℕ`, which is a TYPE, and reading it as a relation is
exactly how the erdos124 capture would have been waved through. A Prop with no relation
symbol (`(hp : Prime p)`) therefore falls through to the **refusal**, not to a silent
re-bind.

Universal closure remains sound even when it shadows a parent binder of the same name: the
conjunct is a CLOSED statement and is exactly the theorem the child elaborated. The unsound
move — the only one this function used to make — is **dropping** a binder that is not the
parent's.

### 2. GATE 4 catches the refusal; nothing reaches the box

`composition_lean` now returns `(text, statement, flags)` and propagates the refusal. At the
GATE 4 call site the refusal is caught, `_comp_refusal` is banked, and the node is skipped —
**no Lean process is spent on a composition the emitter should not have written**.

### 3. The verdict is an EMITTER refusal, never a mathematical one

`_composition_node` banks a refused composition as

```json
{"verdict": "COMPOSITION_BINDER_MISMATCH", "lane": "EMITTER_REFUSAL",
 "counts_toward_parent": 0, "binder_mismatch": {...both types...},
 "note": "THIS IS NOT A MATHEMATICAL OUTCOME ... Do NOT read this as COMPOSITION_OPEN."}
```

and every composition node now carries `composition_extra_hypotheses` — empty when every
surviving child's binders were the parent's own, compared by name AND type; non-empty when
the implication is weaker than `children → parent`. That is the field a consumer reads to
know it must not treat the parent as licensed by the children alone.

---

## PROBE, AFTER

`fix-compose/probe04_after.py` — probe 04 with the one corrected call
(`AFTER-probe04-fixed.log`):

```
  SAME NAME, DIFFERENT TYPE            parent['(n : ℕ)'] child['(n : ℚ)']
      REFUSED -> COMPOSITION_BINDER_MISMATCH: the child binds `n` at type `ℚ`; the parent
      binds the same name at type `ℕ`. A shared NAME is not a shared BINDER. ...

  LIVE (a) erdos1085#D6                parent[... '(hd : 1 ≤ d)' ...] child[... '(hd : 4 ≤ d)' ...]
      conjunct emitted -> (∀ (hd : 4 ≤ d), P d n)
      FLAG COMPOSITION_EXTRA_HYPOTHESIS: child `4 ≤ d` vs parent `1 ≤ d`

  LIVE (b) erdos124#D1                 parent['(r : ℕ)', '(d : Fin r → ℕ)'] child['(d : ℕ)', ...]
      REFUSED -> COMPOSITION_BINDER_MISMATCH: the child binds `d` at type `ℕ`; the parent
      binds the same name at type `Fin r → ℕ`. ...

B. WHAT THE WHOLE COMPOSITION FILE NOW SAYS
  NOTHING IS EMITTED.  COMPOSITION_BINDER_MISMATCH: ...
```

The probes as banked (`hunt3/probe04*.py`) still pass the **old** argument shape. Run
verbatim, `probe04` now universally closes everything in part A and part B **raises**
`CompositionBinderMismatch` (`AFTER-probe04-verbatim.log`) — the old calling convention
fails loudly rather than silently, which is the point. `probe04b` reads the sidecars off
disk, so it is unaffected by the API and is the live-status probe; see the census below.

---

## THE TWO LIVE SIDECARS, RE-EMITTED

`fix-compose/reemit.py` (dry-run first: `DRY-reemit.log`; applied: `APPLY-reemit.log`).
Deterministic, no kernel, no model. **Nothing was deleted.**

### `erdos1085:B:M01#COMPOSE` — RE-STATED

The D6 conjunct now carries its own hypothesis. Exact delta, 16 characters
(`AFTER-statement-delta.log`):

```
insert   BEFORE[764:764]=''
         AFTER [764:780]='∀ (hd : 4 ≤ d), '
  context: ... ≤ (unitPairs 3 s : ℝ))) ∧ (∀ (hd : 4 ≤ d), (∀ s : Finset (EuclideanSpace ...
```

| | before | after |
|---|---|---|
| `gate4_verdict` | `COMPOSITION_OPEN`, rc=1, `unsolved goals` | `COMPOSITION_NOT_RUN` — "the kernel has never seen THIS text" |
| `composition_extra_hypotheses` | absent | `[COMPOSITION_EXTRA_HYPOTHESIS]`, both propositions named |
| `lean_file_sha256` | `f4d7d756a018…` | `c78c44c459cb…` |
| `counts_toward_parent` | 0 | 0 (unchanged) |

The `.lean` GATE 4 actually ran is preserved beside it as
`erdos1085_B_M01_COMPOSE.superseded-g5.lean`, and the verify arm re-hashes it to the banked
sha. The new verdict is **NOT_RUN**, not a pass: this text has never been compiled, and
saying otherwise would be the same disease one level up.

### `erdos124:LEM:R007:L1#COMPOSE` — REFUSED

| | before | after |
|---|---|---|
| `gate4_verdict` | `COMPOSITION_OPEN`, rc=1, `Application type mismatch` ×2 | `COMPOSITION_BINDER_MISMATCH`, `lane: EMITTER_REFUSAL`, both types named |
| `statement` | the 348-char implication over a re-typed `d` | `(composition not constructed)` |
| `lean_signature` / `lean_file_sha256` / `source` | present | **removed** — nothing is offered for a composition that was not stated |

The defective `.lean` is left on disk exactly as GATE 4 ran it, named in the supersession
block with `"do not compile it as one"`. Nothing points at it any more.

### The supersession record

Both nodes carry `emitter_defect_supersession` with `class: EMITTER_DEFECT_SUPERSEDED`, the
finding id, the previous verdict, statement, signature, sha and source, and *why* the old
row must not be read as a result about the mathematics. The same block was stamped onto both
`receipts/*.composition.json`, whose `verdict` fields are untouched.

**One honest side effect, recorded not hidden:** the re-emission uses **today's**
`lean_preamble`. `open scoped Classical` and `noncomputable section` landed on 2026-09-02,
after these sidecars were written. Splicing a corrected statement under a stale header would
produce a file no version of this emitter ever emits, so the whole file was re-emitted and
`preamble_also_changed: true` is banked with a note. The definitions body is asserted
unchanged before anything is written.

---

## VERIFICATION

`fix-compose/verify.py` → **ALL CHECKS PASS** (`AFTER-verify.log`), 18 arms:

- the child's `4 ≤ d` is in the statement; the flag names both propositions
- `lean_file_sha256` matches the file on disk, and the file **is**
  `lean_preamble + lean_statement_line + "\n" + lean_trailer` — the sidecar's own contract
- both re-emitted nodes still pass `DagBuilder.add` (`validate_nodes`)
- the previous `COMPOSITION_OPEN` rows, statements, signatures and shas are all preserved
- the preserved `.lean` re-hashes to its banked sha
- both receipts stamped, original verdicts intact
- `counts_toward_parent` still 0 for both; no green was created anywhere

Estate census, re-run over all 109 sidecars / 95 COMPOSITION nodes / 111 children:

```
  child binders still DROPPED into a parent binder of the same name: 0
  compositions refused COMPOSITION_BINDER_MISMATCH: 1
  compositions carrying an explicit extra hypothesis: 1
```

Selftest: **113/113 checks pass** (`AFTER-selftest.log`). `python -m py_compile` clean.

---

## THE FIVE NEW ARMS

| arm | proves |
|---|---|
| **108** | a child hypothesis STRONGER than the parent's is carried as an EXPLICIT PREMISE and flagged, never asserted under the parent's weaker one — the erdos1085 shape |
| **109** | a child binder at a DIFFERENT TYPE is REFUSED with BOTH types named, never re-bound — the erdos124 shape |
| **110** | the whole composition is refused, not just the conjunct: `(n : ℚ)` under a parent `(n : ℕ)` never reaches the box |
| **111** | a clean case still composes: shared binder FREE, genuinely extra one closed, nothing flagged |
| **112** | `Nat` and `ℕ` are the same binder — the refusal does not fire on spelling |

Arms **32** and **33** kept their assertions verbatim; only their *call* was updated to the
corrected parent-binder argument.

---

## WHAT I DID NOT DO, AND WHY

- **No Lean, no model, no fleet.** The re-emitted erdos1085 composition is
  `COMPOSITION_NOT_RUN`. Whether it closes under its honest hypothesis is an open question
  for the next GATE 4 run — the fix does not answer it and does not pretend to.
- **The other 93 composition nodes were not touched.** The census says they carry no
  capture; re-emitting them would churn shas for nothing.
- **The banked hunt3 probes under `oracle/evidence/msl-machine/hunt3-2026-09-02/` were not
  edited** (outside scope). They now fail loudly against the new signature. A follow-up
  should re-point `probe04`'s single `composition_conjunct` call, or bank
  `fix-compose/probe04_after.py` beside them.
- **The multi-name shadow case is unchanged**: a child `(a b : ℚ)` under a parent `(a : ℕ)`
  is still universally closed, because it states exactly the theorem the child elaborated
  and the conjunct is closed. It is documented in the docstring rather than refused; if the
  estate decides shadowing should be refused outright, that is a policy change, not this bug.

## FILES

| file | what |
|---|---|
| `oracle/tools/msl_decompose.py` | the fix + 5 new selftest arms |
| `oracle/evidence/msl-machine/dag/decomp/erdos1085/erdos1085_B_M01.decomp.json` | re-stated composition |
| `…/erdos1085/lean/erdos1085_B_M01_COMPOSE.lean` | corrected file |
| `…/erdos1085/lean/erdos1085_B_M01_COMPOSE.superseded-g5.lean` | the file GATE 4 ran, preserved |
| `…/erdos1085/receipts/erdos1085_B_M01_COMPOSE.composition.json` | stamped |
| `oracle/evidence/msl-machine/dag/decomp/erdos124/erdos124_LEM_R007_L1.decomp.json` | refused composition |
| `…/erdos124/receipts/erdos124_LEM_R007_L1_COMPOSE.composition.json` | stamped |

Scratchpad (`mine/fix-compose/`): `patch1.py` `patch2.py` `patch3.py` `newblock.py`
`reemit.py` `verify.py` `probe04_after.py` `showdiff.py` `showins.py` `diffpre.py`,
`msl_decompose.BEFORE.py`, `sidecar-1085.BEFORE.json`, `sidecar-124.BEFORE.json`, and every
log named above.
