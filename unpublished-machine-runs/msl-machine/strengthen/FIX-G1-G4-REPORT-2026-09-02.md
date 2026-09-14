# COUNTER-AGENT — HUNT 3, G1 / G2 / G3 / G4 CLOSED

**2026-09-02.** Four findings from `MINE\hunt3\HUNT3-REPORT.md` repaired in
`oracle/tools/msl_strengthen.py` and in `type_gate` (its token table + its arms) inside
`oracle/tools/msl_obligation_dag.py`. $0 — no model call, no Lean, no box, no git.

Every probe the hunter wrote for these four was run **BEFORE** and **AFTER** the repair and
**every one flipped**. Selftests: strengthen **36 → 52 arms, all GREEN** (16 new, at least
one per finding). Every importer of `type_gate` re-run and green.

---

## THE FOUR, EACH WITH ITS PROBE FLIP

### G1 (HIGH) — the model wrote part of the ruler it was measured with

`gate_t` built **both** sides of its type comparison as `definitions + statement`, and
`definitions` was the target's block **plus the model's own `definitions` field**, copied
verbatim off the proposal JSON. Every type the model wrote there cancelled the same type on
the reference side. It also never stripped Lean comments, so a comment sufficed.

**Fix.** The reference is now built from the **canonical target statement + the ESTATE's own
definitions block only**; `gate_t` takes the model's block as a separate
`proposal_definitions` argument that is **never judged** and is banked as a
`counterfactual_with_proposal_definitions` block instead. Comments are blanked on **both**
sides by calling `msl_decompose._d_strip_comments` — the same stripper GATE 0A already uses,
not a second one. ARM 1 is judged on **P' alone**.

**Probe `probe01b_gatet_defs.py` (the hunter's own), on the module's own tuxedo fixture:**

| model-authored `definitions` block | BEFORE | AFTER |
|---|---|---|
| *(empty — the selftest's condition)* | REJECTED | REJECTED |
| `-- every sum here is taken over (1 : ℚ)` (a COMMENT) | **PASS** | **REJECTED** |
| `def msl_scratch (m : Nat) : Rat := (0 : ℚ)` | **PASS** | **REJECTED** |
| `/-- coefficients live in (2 : ℚ) -/` | **PASS** | **REJECTED** |

**Live: `probe02_gatet_live.py` — 8/8 live candidates still PASS, 0 flips.** The guard was
defeatable, not defeated; closing it costs no live candidate.

### G2 (MED-HIGH) — the arm the docstring names had never fired

`type_gate` suppressed its untyped-arithmetic branch whenever any "type token" was present,
and the table counted the **bare word `Finset`** as a type. Every statement this organ
handles is a sum over `Finset.range`/`Finset.Icc` by construction, so the arm was dead on
arrival. A second defect in the same function: with a reference supplied and anything
missing, it returned before the arithmetic check ever ran.

**Fix.** `TYPE_TOKEN` is left alone (it is a **recall** table and is the right unit for
"what did the candidate drop"). A new `TYPE_EVIDENCE` demands a real **typing position** — a
colon, then a carrier type inside the same ascription/binder span — with a trailing
`(?![A-Za-z0-9_'.])` that separates the type `Nat` from the namespace `Nat.succ`. Only
`TYPE_EVIDENCE` or a real `ASCRIPTION` suppresses the arm. **Both arms now always run** and
`missing` is their union, so an inherited drop can no longer hide untyped arithmetic.

**Probe `probe01_strengthen_gates.py` section A — every row flipped:**

| statement | BEFORE | AFTER |
|---|---|---|
| `∑ i ∈ Finset.range n, (1 / 2) ^ i = 2 - 2 * (1 / 2) ^ n` *(the fixture)* | ok=True | **ok=False** |
| `Finset.card (Finset.range n) = n  -- and 1/2 + 1/3 = 5/6` | ok=True | **ok=False** |
| `∀ x, x ∈ Finset.range n → 1/2 * x ≤ 2` | ok=True | **ok=False** |
| `Nat.succ 0 = 1 ∧ 1/2 + 1/3 = 5/6` | ok=True | **ok=False** |
| `(1/2 + 1/3 : ℚ) = 5/6`, `(n * (n+1) : Nat) = n + 2`, `∀ m : Nat, …` | ok=True | ok=True |

Both-arms-run, on the DAG's own arm-47 case:

```
BEFORE  (False, ['type Icc', 'type ℚ', 'ascription (... : ℚ)'])
AFTER   (False, ['<no type ascription on an arithmetic statement>',
                 'type Icc', 'type ℚ', 'ascription (... : ℚ)'])
```

**Live blast radius, measured read-only over 7,157 live DAG statements
(`probe_blast.py`): 32 now REJECTED, 0 newly accepted.** 31 of the 32 are English **prose**
rows carrying untyped arithmetic (`2^a·3^b ≤ 1000`, `141/99 > √2`, `t₁=1/2`) — exactly the
population `binding=UNBOUND` exists to keep the manufacturing loop off. The 32nd is a real
Lean statement and is a **true catch**:

```
erdos289:KER:Erdos289Head:W4_fragment
  theorem W4_fragment : ∀ a ∈ Icc 5 60, ∀ b ∈ Icc (a + 1) 60, runSum a b ≠ 1 / 6
```

`1 / 6` carries no ascription; it is the same family the DAG's own arm 47 uses as its
negative example. The verdict is fail-closed and recoverable by writing `(1 / 6 : ℚ)`.
Nothing already banked is rewritten — the change affects verdicts stamped from here on.

### G3 (MED-HIGH) — `VERIFIED_THEOREM` was stamped off the implication lemma's axioms

`composed_lean` emits **four** `#print axioms` commands; `composed_verdict` read the
footprint with `AXIOM_LINE.search`, which returns the **first** match in the log — the
implication lemma's. `final_name` was used only inside error strings.

**Fix.** The footprint is keyed **by declaration name** through `msl_ladder.axioms_in` (the
estate's existing decl → axioms reader; nothing re-derived here). `final_name` must have a
line of its own — absent is a **refusal**, never a pass — and **every** declaration in the
file must be clean. The verdict now carries `final_theorem` and the full `axiom_footprints`
map.

**Probe `probe01_strengthen_gates.py` section C — the dangerous direction flipped:**

```
log: th_impl/th_base clean; th_step/th_all/th_composed carry Lean.ofReduceBool + Lean.trustCompiler
BEFORE  {"verdict": "VERIFIED_THEOREM", "axioms": ["propext","Classical.choice","Quot.sound"]}
AFTER   {"verdict": "COMPOSITION_FAILED", "final_theorem": "th_composed",
         "axioms": [... "Lean.ofReduceBool", "Lean.trustCompiler" ...],
         "kernel_error": "AXIOM.DIRTY {\"th_all\":[...], \"th_composed\":[...], \"th_step\":[...]}"}
```

The mirror (dirty implication lemma, clean final theorem) still fails — correctly, since all
four end up inside the final theorem's footprint — but now **names `th_impl`** instead of
silently reporting the wrong declaration's axioms.

### G4 (MED-HIGH) — the strengthener rebuilt its own header and dropped three structural lines

`preamble` wrote its own header: `open Finset` instead of `open Finset BigOperators`, no
`open scoped Classical`, no `noncomputable section` — the two lines `msl_decompose` had just
bought with a 41-sidecar census (12 `synthInstanceFailed` + 12 `dependsOnNoncomputable`).
0 of 78 live `.lean` files carried any of them, and there was no GATE 0 here, so a shared
header failure was attributed to **N candidates individually**.

**Fix.**
1. `preamble` now calls **`dec.lean_preamble(defs, set_options=extra_options)`** verbatim and
   adds only the two local `abbrev` lines.
2. `preamble_contract_defects` **asserts** the contract (autoImplicit, maxRecDepth,
   `PREAMBLE_OPEN`, `PREAMBLE_CLASSICAL`, and `NONCOMPUTABLE_OPEN` whenever there is a defs
   body). A miss raises `PREAMBLE_CONTRACT_BROKEN` — a machinery failure, never a candidate's.
3. **GATE 0A (static, $0):** `dec.repair_defs` then `dec.defs_static_defects` on the shared
   block. Defects → the **TARGET** is refused `GATE0A_STATIC_DEFINITIONS`, zero kernel jobs.
4. **GATE 0 (kernel):** one `<tag>__defs` job built by `dec.defs_probe_lean(defs)` before
   BATCH 1. Failure → the TARGET is refused `GATE0_DEFINITIONS` and each candidate carries
   `REFUSED_GATE0_DEFINITIONS`; `dropped_no_elaboration` is not reported at all.
5. BATCH 1 asserts the candidate file **starts byte-exactly** with the header GATE 0
   certified (`PREAMBLE_DIVERGENCE`), the same runtime guard `msl_decompose:2306` uses.

**Probe `probe03_preamble_divergence.py`:**

| | BEFORE | AFTER |
|---|---|---|
| `open Finset BigOperators` in `st.preamble` | False | **True** |
| `open scoped Classical` in `st.preamble` | False | **True** |
| `noncomputable section` in `st.preamble` | False | **True** |
| unified diff of the header lines | 5 removals / 3 additions | **empty** |
| `calls dec.lean_preamble` | False | **True** |
| `calls dec.defs_static_defects` | False | **True** |
| `calls dec.repair_defs` | False | **True** |

---

## THE 16 NEW SELFTEST ARMS (strengthen: 36 → 52, all GREEN)

```
S9   G1 a model-authored `definitions` comment can no longer cancel GATE T
S9b  G1 a Lean COMMENT types nothing on EITHER side (comments stripped)
S9c  G1 a model-written DEFINITION no longer cancels the reference, and what it WOULD
        have done is banked as a counterfactual rather than acted on
S9d  G2 ARM 1 (the tuxedo proper) bites the untyped fixture ON ITS OWN
S9e  G2 a NAMESPACE word is not a type; a real ascription is
S9f  G2 both arms always run: an inherited drop no longer hides untyped arithmetic
S10  G3 a composed log whose FINAL theorem carries sorryAx is NOT verified, however
        clean its lemmas are                                   <- the arm the brief demanded
S10b G3 a DIRTY final theorem is not stamped off a clean implication lemma
S10c G3 the MIRROR: a dirty LEMMA still fails, and the verdict names the lemma
S10d G3 a MISSING footprint for the final theorem is a refusal, never a pass
S10e G3 a green verdict carries the FINAL theorem's name and every footprint read
S11  G4 the assembled header carries every structural line the census bought
S11b G4 GATE 0's probe is a byte-exact PREFIX of the file a candidate is judged in
S11c G4 the contract is CHECKED, not assumed: the old hand-built header is reported
        missing all three lines
S11d G4 a statically broken SHARED block refuses the TARGET and reaches NO kernel job
S11e G4 a shared block that does not ELABORATE refuses the TARGET as GATE0_DEFINITIONS
        -- never N candidates DROPPED_DOES_NOT_ELABORATE
```

## EVERY `type_gate` IMPORTER, RE-RUN

| module | before | after |
|---|---|---|
| `msl_ore_ingest.py` (the door) | 117/117 | **124/124** \* |
| `msl_promote.py` (the sweeper) | 88/88 | **88/88** |
| `msl_decompose.py` | 108/108 | **113/113** \* |
| `msl_ladder.py` | 38/38 | **38/38** |
| `msl_obligation_dag.py` (the DAG) | 70/70 | **70/70** |
| `msl_strengthen.py` | 36/36 | **52/52** |
| `msl_machine.py` | 33/33 | **33/33** |

\* `msl_ore_ingest` and `msl_decompose` grew arms **under me, from another agent**, during
this window (decompose's five are HUNT 3 / G5, the binder-capture repair). Neither count
change is mine and both are green. `msl_strengthen --problem erdos289 --dry-run` still
plans 4 proposer calls / 96 kernel jobs and spends nothing.

## FILES TOUCHED (write scope, nothing else)

- `oracle/tools/msl_strengthen.py` — `preamble` + `PREAMBLE_CONTRACT` +
  `preamble_contract_defects` (G4), `_tg_unit` + `gate_t` (G1), `composed_verdict` (G3),
  `run_target` GATE 0A / GATE 0 / the GATE T call site, `import msl_ladder as ladder`,
  16 selftest arms and two fixtures.
- `oracle/tools/msl_obligation_dag.py` — **only** `TYPE_EVIDENCE` (new, beside the token
  table) and the `type_gate` function.
- No writes under `oracle/evidence/msl-machine/strengthen/` other than the selftest's own
  `_selftest` workspace, which the module already used.

## WHAT I DID NOT DO

- **G5** (child binder capture by name, `msl_decompose`) is outside my write scope; another
  agent landed it during this window — arms 108-112 are theirs.
- **G9** (`--selftest` writing canned kernel receipts into the live evidence tree) was not in
  the brief and is untouched; `OUT_DIR/_selftest` still receives the fixture receipts, and my
  two new fixtures (`fx7`, `fx8`) both return before BATCH 4, so they add no `.composed.json`.
- The 32 live DAG statements G2 now marks UNBOUND were **not** rewritten. Marking them is the
  gate's stated purpose; re-typing `W4_fragment` as `(1 / 6 : ℚ)` is a separate, deliberate
  edit for whoever owns that node.
