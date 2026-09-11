# Erdős Problem 66 — campaign contract (frozen 2026-09-05)

## Canonical statement (verbatim, erdosproblems.com/66, LaTeX source)

> Is there $A\subseteq \mathbb{N}$ such that
> \[\lim_{n\to \infty}\frac{1_A\ast 1_A(n)}{\log n}\]
> exists and is $\neq 0$?

**Status on source: `OPEN` — "$500" — "This is open, and cannot be resolved with a finite computation."**
Page last edited 06 April 2026; read 2026-09-05.
Tags: `number theory`, `additive basis`.
Sources listed: [Er56][Er59][Er80,p.98][ErGr80][Er85c][Er89d][Er90][Er95][Er97c][Er97f][Va99,1.16].

## Prior art recorded on the source page (verbatim)

> A suitably constructed random set has this property if we are allowed to ignore an exceptional
> set of density zero. The challenge is obtaining this with no exceptional set. Erdős believed the
> answer should be no. In [Er80] he explicitly asked whether there exists such a set where the
> limit is 1 (and did not believe there existed such a sequence).
>
> Erdős and Sárközy proved that
> |1_A * 1_A(n) − log n| / sqrt(log n) → 0
> is impossible. Erdős suggests it may even be true that the lim inf and lim sup of
> 1_A * 1_A(n)/log n are always separated by some absolute constant.
>
> Horváth [Ho07] proved that
> |1_A * 1_A(n) − log n| ≤ (1−ε) sqrt(log n)
> cannot hold for all large n.

**The gap this campaign faces.** Every published impossibility result controls the error term at
scale `sqrt(log n)`. The problem as stated only requires the error to be `o(log n)`. The
state of the art is therefore a full `sqrt(log n)` factor away from a negative close, and no
construction is known for an affirmative close. This campaign did **not** close that gap.

## Formal semantics binding

Formalized upstream at
`google-deepmind/formal-conjectures : FormalConjectures/ErdosProblems/66.lean`
(`@[category research open, AMS 11] theorem erdos_66`, statement body `sorry`, answer `sorry`).

```
∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧ Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)
```

with, from `FormalConjecturesForMathlib/Combinatorics/Additive/Convolution.lean`:

```
def sumConv (f g : ℕ → R) (n : ℕ) : R := ∑ p ∈ antidiagonal n, f p.1 * g p.2
noncomputable def sumRep (A : Set ℕ) : ℕ → ℕ := (𝟙_A ∗ 𝟙_A)
```

**Convolution convention (contract-critical): `sumRep A n` counts ORDERED pairs `(a,b) ∈ A × A`
with `a + b = n`, diagonal term `a = b` included with multiplicity one.** The `Erdos66.rep`
definition used in this campaign's Lean is bound to that convention by the kernel-checked lemma
`rep_eq_sumConv`, which proves `rep A n = ∑ p ∈ antidiagonal n, 1_A p.1 * 1_A p.2` — the
literal right-hand side of the upstream `sumRep`. `ℕ` includes `0` under both conventions.

## Close branches

- **A (affirmative):** exhibit `A ⊆ ℕ` and `c ≠ 0` with `r_A(n)/log n → c` along the full
  sequence `n → ∞`, no exceptional set of any density permitted.
- **B (negative):** prove that for every `A ⊆ ℕ`, `r_A(n)/log n` fails to converge to any
  nonzero limit. Note the negation is about a *full limit*, not a limsup/liminf statement.

## Non-results (this campaign holds itself to these)

- A density-one / exceptional-set-permitted construction. The source page already records that
  this exists; it is not the problem.
- Any finite computation over finite `A ⊆ [0,N]`. The source states the problem cannot be
  resolved by finite computation, and no finite-reduction theorem is known.
- Control of the error term at scale `sqrt(log n)` — already published (Erdős–Sárközy, Horváth).
- Replacing `lim` by `limsup`/`liminf`.

## What this campaign banks

Kernel-checked (sorry-free Lean, Mathlib `v4.31.0-rc1`) elementary structure theory for any
hypothetical witness, plus an exhaustive finite verification of the exact combinatorial
identity the Lean rests on. **The target remains UNRESOLVED.** See `FINDINGS.md`.
