# Erdős Problem 40 — campaign contract (frozen 2026-09-05)

## Canonical statement (verbatim, erdosproblems.com/40, read 2026-09-05)

> For what functions $g(N)\to \infty$ is it true that
> \[\lvert A\cap \{1,\ldots,N\}\rvert \gg \frac{N^{1/2}}{g(N)}\]
> implies $\limsup 1_A\ast 1_A(n)=\infty$?

**Status on source: `OPEN` — "This is open, and cannot be resolved with a finite computation."
— `$500`.**
Sources listed: `[Er95] [Er97c]`. Tags: `number theory`, `additive basis`.
Additional thanks: Sarosh Adenwalla. Proof expositions: 0. Comments: 0. Proof claims: 0.

## Prior art recorded on the source page (verbatim, and it is ALL of it)

> This is a stronger form of the Erdős-Turán conjecture [28] (since establishing this for any
> function $g(N)\to \infty$ would imply a positive solution to [28]).

**That single sentence is the entire body of the page.** The source records NO function `g` for
which the implication is known to hold, and NO function `g` for which it is known to fail. There
is no published partial result quoted, and no `g` is named anywhere on the page.

## Formal semantics binding

Formalized upstream at
`google-deepmind/formal-conjectures : FormalConjectures/ErdosProblems/40.lean`
(`@[category research open, AMS 11] theorem erdos_40 : Erdos40ForSet answer(sorry)`, body `sorry`):

```lean
def Erdos40For (g : ℕ → ℝ) : Prop :=
  ∀ A : Set ℕ,
    (fun N : ℕ ↦ √N / g N) =O[atTop] (fun N ↦ ((A ∩ .Icc 1 N).ncard : ℝ)) →
    limsup (fun N ↦ (sumRep A N : ℕ∞)) atTop = ⊤

def Erdos40ForSet (G : Set (ℕ → ℝ)) : Prop := ∀ g ∈ G, Tendsto g atTop atTop → Erdos40For g
```

with, from `FormalConjecturesForMathlib/Combinatorics/Additive/Convolution.lean`:

```lean
def sumConv (f g : ℕ → R) (n : ℕ) : R := ∑ p ∈ antidiagonal n, f p.1 * g p.2
noncomputable def sumRep (A : Set ℕ) : ℕ → ℕ := (𝟙_A ∗ 𝟙_A)
```

**Convolution convention (contract-critical): `sumRep A n` counts ORDERED pairs `(a,b) ∈ A × A`
with `a + b = n`, diagonal term `a = b` included once.** This campaign's `Erdos40.rep` is bound
to that convention by the kernel-checked `rep_eq_sumConv`; this campaign's `Erdos40.cnt` is bound
to the upstream `(A ∩ Set.Icc 1 N).ncard` by the kernel-checked `ncard_eq_cnt`. `ℕ` includes `0`
under both conventions, and the counting window `Icc 1 N` excludes it.

**Note on the upstream `answer(sorry)`.** Erdős 40 is an "answer" problem: what is being asked for
is the SET of admissible `g`, not the truth of a fixed proposition. A close therefore means
identifying that set. This campaign pins the set from two sides; it does not identify it.

## Close branches

- **A (an answer exists):** exhibit a single `g` with `g(N) → ∞` and `Erdos40For g`. By the
  source's own remark — and by this campaign's `erdos28_of_erdos40For` — this branch is at least
  as hard as the Erdős–Turán conjecture (Erdős Problem 28, also open, also `$500`).
- **B (the answer set is empty):** show that for every `g → ∞` there is a set `A` with
  `|A ∩ [1,N]| ≫ √N/g(N)` and bounded representation function. By `erdos40For_iff` this is
  exactly the statement that infinite `B₂[k]` sets of counting function `≫ √N/g(N)` exist for
  every `g → ∞` — an open question in its own right (the dense infinite Sidon set problem).

## Non-results (this campaign holds itself to these)

- Any finite computation about `Erdos40For` itself. The source states the problem cannot be
  resolved by a finite computation, and no finite-reduction theorem is known.
- The trivial instantiation `g = √N` used upstream in `erdos_40.variants.implies_erdos_28`:
  it makes the density hypothesis vacuous and proves nothing about a `g` of interest.
- Improving the ceiling by *asserting* a dense Sidon construction. Mian–Chowla
  (`A(N) ≫ N^{1/3}`) and Ruzsa (`A(N) ≫ N^{√2−1−o(1)}`) are published and would lower the
  ceiling to `N^{1/6}` and `N^{0.086…}` respectively — **neither is formalised here**, and both
  are recorded as UNPROVED in `receipts/findings.json`. The socket for them is the banked
  `not_erdos40For_of_dense_sidon`.

## What this campaign banks

Kernel-checked (sorry-free Lean, Mathlib `v4.31.0-rc1`) structure theory for the answer set:
the semantic bindings, downward closure, an exact reformulation in terms of bounded
representation functions, an unconditional CEILING with an explicit `g → ∞` excluded, and the
FLOOR (a single answer function settles Erdős–Turán). Plus an independent brute-force
verification of every finite claim the Lean rests on.
**The target remains UNRESOLVED.** See `receipts/findings.json`.
