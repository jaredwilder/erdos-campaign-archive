# GATE 0 — the one emitter defect that was holding 41 parents

**Status of the fix: `KERNEL_UNVERIFIED`.** No Lean ran anywhere in this session (remote box
deleted, laptop WSL off limits, no model spend). Everything below is diagnosed from the
kernel's OWN banked error text in the sidecars and verified with offline, string-level
selftests. **A box must re-run the 41 before any of this is called closed.**

- Module changed: `C:\Users\jared\Local Sites\woocommerce-enterprise\oracle\tools\msl_decompose.py`
- `--selftest`: **108/108 PASS** (was 78/78; +30 arms, all offline, no Lean, no network)
- Replay of the 41 real banked blocks through the new gate: **21 caught · 19 closed
  structurally by the preamble · 1 residual**
- False-positive guard: replayed against all **47** blocks the kernel ACCEPTED →
  **0 touched, 0 refused**

---

## 1. THE ERROR-CLASS TABLE (all 41, read off the banked `kernel_error` strings)

`oracle\evidence\msl-machine\dag\decomp\*\*.decomp.json`, `definitions.gate0.kernel_error`.
Six classes, no long tail. Counts are per sidecar; a sidecar can carry two classes.

| # | Lean error class | sidecars | example (verbatim from the kernel) |
|---|---|---|---|
| C1 | `lean.dependsOnNoncomputable` | **12** | *"failed to compile definition, consider marking it as 'noncomputable' because it depends on `Nat.nth`"* — erdos208, `def s : ℕ → ℕ := fun n => Nat.nth (fun k => Squarefree k) n` |
| C2 | `lean.synthInstanceFailed` | **12** | *"failed to synthesize instance of type class `DecidablePred fun k => k ∈ A`"* — erdos456; also `Fintype (ℕ × ℕ)`, `HAdd ((ℕ → ?m) → ?m) ℕ ℕ` |
| C3 | `lean.unknownIdentifier` — **Unknown constant** | **6** | ``Unknown constant `Nat.sigma` `` — erdos830; also `Nat.partitions`, `Nat.factors`, `Nat.Composite`, `Complex.conj` |
| C4 | `lean.unknownIdentifier` — **Unknown identifier** | **8** | ``Unknown identifier `k` `` + *"not possible to treat `k` as an implicitly bound variable … `autoImplicit` is `false`"* — erdos1056; also `ω`, `Ω`, `n!`, `nth`, `Q`, `i`, `j` |
| C5 | `lean.invalidField` | **2** | *"Invalid field `IsSierpinskiNumber`: the environment does not contain `Nat.IsSierpinskiNumber`"* — erdos1113 |
| C6 | parse / `Function expected` (no code) | **4** | `unexpected token 'in'; expected ','` (erdos1101) · `Function expected at` (erdos289) · `expected token` (erdos853) · `unexpected token '+'` (erdos936) |

The frequency table of what the noncomputable errors NAMED is itself the diagnosis:
`Nat.instInfSet` ×3 · `Nat.nth` ×3 · `Real.decidableLT` ×2 · `Real.instPow` ×2 ·
`Real.instDivInvMonoid` ×2 · `Real.decidableEq` · `Nat.card` ·
`instConditionallyCompleteLinearOrder` · `propDecidable` · `tprod`.
**Only 3 of the 41 blocks wrote `noncomputable` themselves.** This is a header, not mathematics.

### The one that is not a typo — and it is Mathlib's, not the proposer's

`∑ x ∈ s, e` and `∏ x ∈ s, e` parse their **body at precedence 67** (`notation3 … r:67`).
`+` and `-` sit at **65**. So

```lean
(∏ i ∈ Finset.Icc (1 : Nat) k₁, n₁ + i).primeFactors      -- erdos931, verbatim
```

means `(∏ i ∈ Icc 1 k₁, n₁) + i` — the product loses its body and `i` escapes the binder.
Under `autoImplicit false` that is exactly the banked ``Unknown identifier `i` `` at 10:41 and
``Unknown identifier `j` `` at 11:43. Where the escaped operand is the sum itself, it comes
back instead as `failed to synthesize HAdd ((ℕ → ?m) → ?m) ℕ ℕ` — three more sidecars.
`*` (70), `/` (70) and `^` (75) bind **tighter** and are safe, which is precisely why the
sidecars that used them (erdos124, `∑ i ∈ s, d ^ (i : ℕ)`) elaborated cleanly.

---

## 2. THE FIX, PER CLASS

### 2a. Two structural lines in `lean_preamble` — 24 of 41, closed for every future block

```lean
import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open scoped Classical            <-- NEW  (PREAMBLE_CLASSICAL)

noncomputable section            <-- NEW  (NONCOMPUTABLE_OPEN)

<the definitions block>

end                              <-- NEW  (NONCOMPUTABLE_CLOSE)
```

| class | fix | why it is sound |
|---|---|---|
| **C1** noncomputable | `noncomputable section` wraps the block | Mathlib's own idiom: it *permits* noncomputable defs without erroring on the computable ones beside them, which a blanket `noncomputable` modifier would. Nothing here ever runs compiled code. |
| **C2** missing instance | `open scoped Classical` | Low-priority `Classical.propDecidable`; a real `DecidablePred` instance still wins. erdos1145 is the proof of the pair: its proposer *did* write `open Filter Classical`, which fixed the synth and then exposed the noncomputability — the two fixes are complementary halves of one header. |

⚠️ **Recorded hazard, banked on every sidecar** (`definitions.preamble_carries`):
elaboration under this preamble is **no longer a decidability witness**.
`fireable_decidable_leaves` is read off `leaf_tactic_hint`, never off "it compiled" — that
must stay true, and a `decide` leaf that elaborates classically can still fail to reduce.

### 2b. GATE 0A — a string gate that runs BEFORE any Lean process

New in the module: `repair_defs(defs)` and `defs_static_defects(defs)`, wired into
`Decomposer.run` **before** the defs job is queued. A statically-defective block is never
sent to the box (`kernel_calls_saved: 1` on the receipt) and each child is rejected naming
**its class** — `GATE0A_D6` — instead of the anonymous `GATE0_DEFINITIONS` that made 41
parents look like 41 mathematical failures.

**The repair licence is narrow and stated in the code:** a rewrite is applied only where the
unrepaired text *could not have elaborated at all*. We are never choosing between two
readings; we are writing down the only reading that has one.

| class | R/F | what it catches | measured on |
|---|---|---|---|
| **D1** `BIGOP_BODY_PRECEDENCE` | REPAIR | `∑/∏ x ∈ s, a + b` → `∑/∏ x ∈ s, (a + b)`, only when the loose operand uses a bound name | erdos931 (+3 as `HAdd`) |
| **D2** `BIGOP_DEPRECATED_IN` | REPAIR | `∑ x in s,` → `∑ x ∈ s,` | erdos1101 |
| **D3** `ASCII_PSEUDO_LEAN` | REFUSE | `/\`, `\/`, `!=`, `Forall`, `Exists`, `Nat x Nat` | erdos289 |
| **D4** `ASCII_TYPE_NAME` | REFUSE | `(c : Q)` → names `ℚ` (also `R Z N C`) | erdos424 |
| **D5a** `TRANSPORT_CHARACTER` | REPAIR | NBSP, thin/zero-width space, fullwidth punctuation, smart quotes, U+2212 minus, U+2215 slash | prophylactic |
| **D5b** `UNICODE_LOOKALIKE` | REFUSE | `∠` (U+2220) where `∧` (U+2227) was meant. **Not** repaired — substituting an operator is substituting mathematics. `Π`/`Σ` are deliberately absent from the table: they are legal Lean. | erdos853 |
| **D6** `UNKNOWN_MATHLIB_NAME` | REFUSE | `Nat.partitions`, `Nat.factors`→`Nat.primeFactorsList`, `Nat.Composite`, `Nat.sigma`, `Complex.conj`, `Nat.find?`, `Nat.eraseDups` — each with the spelling that IS in Mathlib | erdos1106, 1113, 830, 507, 853 |
| **D7** `DOT_NOTATION_ON_LOCAL_DEF` | REPAIR | `m.IsSierpinskiNumber` → `IsSierpinskiNumber m` when the name is a top-level def in this block (so it lives in no namespace and the dotted form can never resolve) | erdos1113 |
| **D8a** `FACTORIAL_SCOPED_NOTATION` | REPAIR | `n !` / `n!` → `(Nat.factorial n)`; the postfix is scoped in `Nat`, which this preamble deliberately does not open (`open Nat` makes `gcd` ambiguous — measured on the box) | erdos1108, erdos936 |
| **D8b** `SCOPED_NOTATION_NOT_OPEN` | REFUSE | `ω`/`Ω` (→ `ArithmeticFunction.cardDistinctFactors` / `cardFactors`), bare `nth` (→ `Nat.nth`) | erdos306, erdos938 |
| **D9** `FREE_VARIABLE_SHAPED_NAME` | REFUSE | a variable-shaped name (1–2 lowercase chars + subscripts) nothing binds, anywhere in the block | erdos289, erdos1101 |
| **D9b** `FREE_VARIABLE_IN_SIGNATURE` | REFUSE | a free name in a def's **own** signature, checked against that signature's **exact** binders | erdos1056 (`Fin (k : Nat)`) |
| **D10** `FORWARD_REFERENCE` | REFUSE | a def using a name defined lower in the block (Lean does not hoist) | prophylactic |
| **D11** `DUPLICATE_DEFINITION` | REFUSE | a name declared twice in one block | erdos456 |
| **D12** `NO_EXPLICIT_RESULT_TYPE` | REFUSE | `def f := …` — the TUXEDO LAW one level up from an untyped numeral | erdos188 |

Two more defects were found and fixed while doing this:

- **`ERROR_LINE` could not see a single one of these errors.** It matched `error:`; every
  banked diagnostic is `error(lean.unknownIdentifier):`. All 41 were caught only by
  `rc != 0`, and the banked text came from the `dlog[-1500:]` fallback. **A Lean run that
  printed typed diagnostics and exited 0 would have scored `DEFS_ELABORATE`.** Widened to
  `error(?:\([^)]*\))?:`.
- **`defs_probe_lean` now asserts the byte-identity contract**: what GATE 0 compiles must be
  a byte-exact *prefix* of the statement files the block ships in, or it raises
  `PREAMBLE_DIVERGENCE`. Without that assertion this very session's preamble change would
  have let GATE 0 keep compiling the old header while the children compiled the new one.

### 2c. The proposer prompt

Law 5 now renders **the live `lean_preamble` output**, generated from the same function the
kernel gets, so the prompt and the file cannot drift. (It previously said "the file begins
with `import Mathlib` and `open Finset`" while the file carried five more lines — which is
how a proposer writes `open Nat` notation into a header that has no `open Nat`.)

A new **law 5b** forbids the nine measured classes by name, each with the correct spelling,
and closes with: *you do NOT need to write `noncomputable`, and you do NOT need to worry
about `Decidable` instances — the header above carries them.*

---

## 3. SELFTEST

**108/108 PASS**, all offline, no Lean, no network, `$0`. The 78 pre-existing arms are green
and untouched. 30 new arms, one per class plus the guards:

| arms | what they hold down |
|---|---|
| 78–81 | preamble carries `noncomputable section` · an empty block opens no section · preamble carries the classical instance · **GATE 0's header is a byte-exact prefix of the statement file** |
| 82–83 | D1 fires on `+` and is repaired · **D1 does NOT fire on `^`/`*`**, which is why the sidecars using them elaborated |
| 84 | D2 `in` → `∈` |
| 85–88 | D3 ASCII pseudo-Lean refused · D4 `(c : Q)` named `ℚ` · D5b `∠` **refused, not substituted** · D5a NBSP repaired |
| 89–91 | D6 `Nat.sigma` · D6 covers renames (`Nat.factors`) · D7 `m.IsSierp` → `IsSierp m` |
| 92–95 | D8a factorial → `Nat.factorial` · D8b `ω`/`Ω` · D8b bare `nth` · **D8b does NOT fire inside `nthPowerful`** (a block the kernel ACCEPTED) |
| 96–97 | D9b signature-exact free variable (erdos1056) · D9 body free variable |
| 98–100 | D10 forward reference · D11 duplicate · D12 no result type |
| 101 | **a clean block is neither repaired nor refused** — the false-positive guard |
| 102–105 | end to end: no `_defs` job reaches the box · the receipt names the class and says a call was saved · **every child is rejected naming the class** · the sidecar warns that elaboration is not a decidability witness |
| 106–107 | the prompt shows the real header · the prompt forbids each class by name |

Two of these arms exist because the first cut of the gate got it wrong on real data, and
both failures are recorded in the code comments:

- `_D_BARE_NTH` fired inside the identifier `nthPowerful` — in **erdos938_B_M01, a block the
  kernel had ACCEPTED**. A gate that refuses accepted work is worse than the defect it was
  added for. (Arm 95.)
- D9 missed erdos1056's free `k`, because the generous body-binder harvest read the
  type-ascription `(k : Nat)` as a binder — the very text that was the bug. Generosity is
  right for a body and wrong for a signature, so D9b scans a signature against its own exact
  binders and nothing else. (Arm 96.)

---

## 4. REPLAY AGAINST THE REAL 41 (no Lean — string level only)

```
CAUGHT by GATE 0A (repair or refusal)                21
STRUCTURAL only (closed by the preamble, no static defect)  19
MISSED                                                1
FALSE POSITIVES over the 47 kernel-ACCEPTED blocks    0
```

Class fire counts across the 41: D6 ×6 · D8b ×4 · D9b ×2 · D9 ×2 · D8a ×2 · D1 · D2 · D3 ·
D4 · D5b · D7 · D11 · D12.

### The one residual, named rather than hidden

**`erdos421_B_M01`** — `(A ∩ Finset.Icc (1 : ℕ) n).card` where `A : Set ℕ`.
Lean: *"Invalid field `card`: the environment does not contain `Function.card` … from an
expression `A ∩ ↑(Icc 1 n)` of type `ℕ → Prop`"*. A `Set` has no `.card`, and deciding that
requires **types**, not strings. GATE 0A cannot catch it offline and does not pretend to;
the prompt names the shape, and the kernel will still catch it as it did. Nothing was
widened to make a coverage number look better.

---

## 5. HOW TO RE-EMIT AND RE-VERIFY THE 41 ONCE A KERNEL BOX EXISTS

**⛔ Do not run any of this without a box. Nothing below was run tonight.**

### Step 0 — prove the preamble itself compiles (do this FIRST, it is one file)

The whole 24-sidecar structural claim rests on two lines. Compile one file before spending
anything:

```bash
python - <<'PY' > /tmp/preamble_probe.lean
import sys; sys.path.insert(0, "oracle/tools")
import msl_decompose as M
print(M.lean_preamble("noncomputable def s : \u2115 \u2192 \u2115 := fun n => Nat.nth (fun k => Squarefree k) n\n"
                      "def cnt (A : Set \u2115) (n : \u2115) : \u2115 := (Finset.filter (fun k => k \u2208 A) (Finset.Icc 1 n)).card"))
PY
lake env lean /tmp/preamble_probe.lean     # MUST be rc 0 with no diagnostics
```

That single file exercises **C1 and C2 together** (`Nat.nth` + `DecidablePred fun k => k ∈ A`).
If it is green, `open scoped Classical` + `noncomputable section` are confirmed against this
Mathlib pin and the `KERNEL_UNVERIFIED` label above can come off for 24 of the 41.
If `open scoped Classical` is rejected by this Mathlib pin, the fallback is
`attribute [local instance 10] Classical.propDecidable` — change `PREAMBLE_CLASSICAL`, one
constant, and re-run `--selftest`.

### Step 1 — zero-spend replay of the 19 STRUCTURAL_ONLY sidecars

These 19 need **no new proposer call**: their banked block is unchanged and only the header
moved. Compile `lean_preamble(banked_block)` for each and read the result. **$0, 19 Lean
runs, no model calls.**

```
erdos1085_A_M01  erdos1101_DEMAND_R003_L2_1  erdos1145_LEM_R004_L1  erdos168_LEM_R005_cert
erdos208_LEM_R004_residual  erdos28_LEM_R008_L1  erdos28_LEM_R008_L1_
erdos340_DEMAND_R002_L1_1  erdos340_LEM_R002_L1  erdos340_LEM_R002_T1  erdos400_A_M05
erdos40_LEM_R005_main  erdos786_LEM_R005_L1  erdos830_LEM_R005_L1_  erdos853_LEM_R002_L1
erdos887_A_M01  erdos887_B_M01  erdos950_LEM_R003_L1  erdos950_LEM_R003_all
```

### Step 2 — re-decompose (this DOES cost one proposer call per node)

`--resume` semantics: `walk_all_prose(..., skip_done=not args.redo)` skips any node whose
sidecar is already on disk, so **the 41 will be skipped unless you either pass `--redo` or
move their sidecars aside.** Prefer moving them aside — `--redo` on `--all-prose` would
re-decompose the whole estate.

```bash
# 1. park the 41 (do NOT delete: they are the evidence this fix was written from)
mkdir -p oracle/evidence/msl-machine/dag/decomp/_gate0-parked-2026-09-02
#    move only the 41 sidecars whose definitions.gate0.verdict == DEFS_DO_NOT_ELABORATE

# 2. re-emit, one problem at a time, budget capped
python oracle/tools/msl_decompose.py --problem erdos1056 --budget-usd 0.10
#    ... 27 problems in total (see the list below)

# 3. or the whole sweep, resuming: everything else on the estate is already done and skips
python oracle/tools/msl_decompose.py --all-prose --budget-usd 3.00 --parallel-problems 3
```

The 27 problems holding the 41: `erdos1056 erdos1085 erdos1101 erdos1106 erdos1108
erdos1113 erdos1145 erdos168 erdos188 erdos208 erdos28 erdos289 erdos306 erdos340 erdos40
erdos400 erdos421 erdos424 erdos456 erdos507 erdos786 erdos830 erdos853 erdos887 erdos931
erdos936 erdos938 erdos950`

### Step 3 — re-measure with the sweeper, do not eyeball it

```bash
python oracle/tools/msl_promote.py --all --dry-run
```

**Pass criterion:** `GATE0_DEFINITIONS` / `GATE0A_*` drops well below 41 in the blocking-gate
table, and `refused=68` falls. **Fail criterion:** a `GATE0A_*` class fires on a block the
kernel would have accepted — that is a false positive and the class must be narrowed, not
the count admired.

---

## 6. WHAT IS AND IS NOT PROVED

**Proved offline, now:** the emitter *sees* the defect the kernel saw, before spending a
kernel call, in 21 of the 41; and it touches none of the 47 blocks the kernel accepted.
108/108 selftest arms, `$0`, 0 model calls, no Lean.

**NOT proved:** that any repaired or re-emitted block actually compiles. `noncomputable
section` and `open scoped Classical` are the documented Mathlib idioms for exactly the two
errors the kernel reported, but **no Lean has confirmed it against this Mathlib pin.** Until
Step 0 above is green, every claim in section 2a is `KERNEL_UNVERIFIED`.

**Scope written:** `oracle\tools\msl_decompose.py` only. No sidecar, no DAG, no evidence file
and no ledger was modified; no sweep was re-run; no box or model was contacted.
