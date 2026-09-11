# Erdős Problem 28 — campaign contract (frozen 2026-09-05)

## Canonical statement

> If `A ⊆ ℕ` is such that `A + A` contains all but finitely many integers (an additive basis
> of order 2), must `limsup_{n→∞} (1_A ∗ 1_A)(n) = ∞`?

This is the **Erdős–Turán conjecture on additive bases** (Erdős–Turán 1941).

**Status on source: `OPEN` — `$500`.** Tags: `number theory`, `additive basis`.
Source: `https://www.erdosproblems.com/28`.

⛔ **SOURCE FETCH FAILED.** `https://www.erdosproblems.com/28` returned **HTTP 403** to this
campaign's fetch on 2026-09-05, so the page body is **NOT** quoted verbatim here and its
comment/proof-exposition counts are **UNKNOWN to this campaign**. The status, prize, tags and
Lean-formalisation flag above are taken from the estate's own ingested target row
(`oracle/evidence/targets/open-frontier.jsonl`, `targetId: erdos:28`, ingested by
`oracle/tools/target_ingest.py` from the teorth/erdosproblems community database).
`FRESHNESS UNKNOWN` — a current status receipt was not obtained.

## Formal semantics binding

Formalized upstream at
`google-deepmind/formal-conjectures : FormalConjectures/ErdosProblems/28.lean`
(local copy read at `oracle/acquisition/formal-conjectures/FormalConjectures/ErdosProblems/28.lean`):

```lean
@[category research open, AMS 11]
theorem erdos_28 (A : Set ℕ) (h : (A + A)ᶜ.Finite) :
    limsup (fun (n : ℕ) => (sumRep A n : ℕ∞)) atTop = (⊤ : ℕ∞) := by
  sorry
```

with, from `FormalConjecturesForMathlib/Combinatorics/Additive/Convolution.lean`:

```lean
def sumConv (f g : ℕ → R) (n : ℕ) : R := ∑ p ∈ antidiagonal n, f p.1 * g p.2
noncomputable def sumRep (A : Set ℕ) : ℕ → ℕ := (𝟙_A ∗ 𝟙_A)
```

**Convolution convention (contract-critical): `sumRep A n` counts ORDERED pairs `(a,b) ∈ A × A`
with `a + b = n`, diagonal term `a = b` included once.** This campaign's `Erdos28.rep` is bound to
that convention by the kernel-checked `rep_eq_sumConv`. `ℕ` includes `0`, and this campaign's
counting window is `[0,N]` (`Erdos28.cnt`), not `[1,N]`.

⚠️ The ORDERED convention is what makes the parity floor of this campaign a bound of `2` rather
than `1`. Under an UNORDERED convention every statement here shifts by a factor of two, and the
comparison with the published record below would change. The convention is frozen with the
target and is not negotiable inside the campaign.

## PROOF_REQUIRES / DISPROOF_REQUIRES

- **PROOF_REQUIRES:** a proof that for EVERY `A` with `(A + A)ᶜ` finite,
  `limsup (sumRep A n : ℕ∞) = ⊤`.
- **DISPROOF_REQUIRES:** an explicit `A` with `(A + A)ᶜ` finite and a single `B` with
  `sumRep A n ≤ B` for all `n` — equivalently (kernel-checked here,
  `erdos28_iff_no_bounded_basis`) a set that is simultaneously an additive basis of order 2
  and a `B₂[B]` set.

## NOT_CLOSURE — the standard floor, imported verbatim, plus three target-specific rows

- a finite computation or table, however large;
- an empirical constant or fit from any finite range;
- improved bounds that do not meet the required bound;
- a reduction to an open statement of comparable difficulty;
- a special case, unless the contract names it as the target;
- a conjecture or heuristic, however well supported.

Target-specific:

- **Any bound `limsup ≥ k` for a fixed finite `k`.** The target is `= ⊤`. In particular the
  floor `≥ 2` proved here closes NOTHING, and neither would matching the published record.
- **A window/finite-interval statement about "covering sets".** A set covering `[1,N]` from
  inside `[0,N]` is not an additive basis of order 2; the two conditions are neither a subset
  nor a superset of one another, and no quantity computed over a window transports.
- **Erdős Problem 40 or any neighbouring answer-set problem.** A related theorem is not this
  target (s.24.31).

## Close branches

- **A (affirmative):** prove `limsup = ⊤` for every basis of order 2. **BLOCKED** — see the
  bottleneck below.
- **B (negative):** construct a basis of order 2 with bounded representation function.
  **BLOCKED** — the same bottleneck from the other side; a counterexample is pinned by
  `counterexample_structure` but not excluded and not constructed.

## The bottleneck this campaign names

**Every route that consumes only (i) positivity of `r_A` on a cofinite set, (ii) the parity of
`r_A` at odd arguments, and (iii) any linear second-moment bound `∑_{n<N} r_A(n)² ≤ C·N`, is
DEAD at the value 2.** Kernel-checked here as `parity_saturates_at_two` and
`parity_and_moment_saturate_at_two`: an explicit function satisfies all three constraints while
never exceeding `2`. `ROUTE_STATUS KILLED_BY_THEOREM`, not `BLOCKED_CURRENT_TECHNIQUE`.

The moment axis is the right one to kill because Ruzsa, *A just basis*, Monatsh. Math. **109**
(1990), 145–151, constructs a genuine additive basis of order 2 with
`∑_{n≤N} r_A(n)² = O(N)`. **CITED, VERIFICATION_DEPTH STATEMENT_MATCHES, NOT formalised here,
and nothing in the banked Lean depends on it.**

## Prior art recorded, and the honest comparison

| result | claim | status here |
|---|---|---|
| Grekos–Haddad–Helou–Pihko (2003) | `σ_A(n) ≥ 6` infinitely often | **CITED, UNPROVED here** |
| Borwein–Choi–Chu (2006), Math. Comp. **75**(253) 475–484 | `σ_A(n) ≥ 8` infinitely often ("cannot be bounded by 7") | **CITED, UNPROVED here** |
| Ruzsa (1990), Monatsh. Math. **109** 145–151 | a basis of order 2 with `∑ r_A(n)² = O(N)` | **CITED, UNPROVED here** |
| **this campaign** | `limsup r_A ≥ 2`, kernel-checked | **PROVED, sorry-free** |

⛔ **THIS CAMPAIGN'S FLOOR IS FAR BELOW THE PUBLISHED RECORD.** The `≥ 2` bound is elementary
and classical in character; what is banked is the machine-checked formalisation, the
counterexample structure theorem, and the two KILL theorems — not a new bound. The `σ_A`
convention (ordered vs unordered) used by Grekos et al. and by Borwein–Choi–Chu was **NOT
verified against the papers themselves** and is recorded as **UNVERIFIED**; the citations were
raised to `STATEMENT_MATCHES` from search snippets only, never from the published text.

## What this campaign banks

Sorry-free Lean (Mathlib `v4.31.0-rc1`), 35 theorems, axiom footprint exactly
`propext, Classical.choice, Quot.sound` on every one:

1. the semantic binding to the upstream `sumRep`;
2. `limsup = ⊤ ↔ r_A unbounded`, and the counterexample-shape reformulation;
3. **THE FLOOR** — `limsup r_A ≥ 2` for every additive basis of order 2;
4. **THE SANDWICH** — a counterexample has `√(N−M) ≤ |A ∩ [0,N]| ≤ √(B(2N+1))`, i.e. `Θ(√N)`;
5. **THE KILLS** — the parity route, and the parity-plus-second-moment route, are each
   consistent with the bound `2` and therefore cannot decide the target;
6. an independent exhaustive finite verification of every finite claim the Lean rests on.

**The target remains UNRESOLVED.** See `receipts/findings.json`.
