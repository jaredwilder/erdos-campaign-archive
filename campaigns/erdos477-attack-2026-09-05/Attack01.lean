import Mathlib

/-!
# Erdős 477 — OB1: the general quadratic rung

Campaign: `erdos477-attack-2026-09-05`.

## Standing asset (frozen, kernel-sealed 2026-09-02)

`campaigns/erdos477-campaign-001/kernel/Erdos477NoSquareTiling.lean`
```
theorem erdos477_no_square_tiling :
    ¬ ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ,
        p.1 ∈ A ∧ (∃ k : ℤ, p.2 = k ^ 2) ∧ n = p.1 + p.2
```
axioms `{propext, Classical.choice, Quot.sound}`.

## OB1 as recorded in the closure-distance ranking

> "All quadratics `ax²+bx+c`. Court-proved (R003: `Δf` covers every integer outside one class
> mod `4|a|`) but not kernel-checked. Type: cheap — finite congruence bookkeeping, the same
> proof with `4` replaced by `4|a|`."

**That cost model is wrong in both directions, and this file records why.**

* R003's claim is FALSE as stated. For `f(x) = x² + x` the difference set is exactly `2ℤ`
  (since `x(x+1)` is always even), whose complement is TWO classes mod `4|a| = 4`, not one.
  For `f(x) = 3x²` the difference set is `3·{M : M ≢ 2 mod 4}`, whose complement contains
  every integer not divisible by 3 — two thirds of ℤ. The mod-`4|a|` bookkeeping does not
  generalise, and for `|a| ≥ 2` the sealed pigeonhole (`|A| ≤ 2`) is simply false:
  `A = {0,1,2}` has all its differences outside `Δ` for `f(x) = 3x²`.

* But the theorem is much CHEAPER than the ranking thought, because the mod-4 mechanism is
  not needed at all. The whole rung falls out of one two-parameter identity:

      f (t + r) - f (r - t) = (4*a*r + 2*b) * t                       (`quad_diff_identity`)

  so the difference set of any quadratic contains the full SUBGROUP `(4*a*r + 2*b)ℤ`, for
  every `r`. Since `a ≠ 0`, at least one of `r = 0` (giving `2b`) and `r = 1` (giving
  `4a + 2b`) yields a NONZERO modulus `N`. Uniqueness of the tiling then forbids `N ∣ α - α'`
  for distinct `α, α' ∈ A`, so `A` injects into `ℤ / N` and is FINITE, hence bounded; while
  `A ⊕ f(ℤ)` must reach arbitrarily far below (`a > 0`) or above (`a < 0`) the bound.

  No congruence bookkeeping, no `a ∣ b` hypothesis, no case split on the parity of `b/a`.

## OB2 (degree ≥ 3) — NOT attacked, recorded only

The mechanism above dies at degree `d ≥ 3`: `f(t+r) - f(r-t)` is no longer linear in `t`,
and the difference set contains no nonzero subgroup (its counting function is `O(R^{2/d})`).
The ranking's verdict "expensive, no mechanism" stands and no budget was spent there.

## Scope note (statement discrepancy, worth recording)

The upstream DeepMind `FormalConjectures/ErdosProblems/477.lean` states its variants over
`f.eval '' {n | 0 < n}` — the values at STRICTLY POSITIVE indices, which for `f = X^2`
excludes `0`. The estate's sealed asset (and therefore this generalisation) quantifies over
`∃ k : ℤ`, i.e. all of `f(ℤ)`. Those are different tiling problems: `4` is a difference of
two squares but not of two POSITIVE squares. This file closes the `f(ℤ)` form; the upstream
positive-index form remains open here.
-/

set_option autoImplicit false

namespace Erdos477Attack

/-! ### Stage 1 — the identity that replaces the mod-4 mechanism -/

/-- The two-parameter difference identity. Evaluating a quadratic at the two points
`r + t` and `r - t`, symmetric about `r`, the square terms cancel their `t²` and the result
is LINEAR in `t` with slope `4*a*r + 2*b`. -/
theorem quad_diff_identity (a b c r t : ℤ) :
    (a * (t + r) ^ 2 + b * (t + r) + c) - (a * (r - t) ^ 2 + b * (r - t) + c)
      = (4 * a * r + 2 * b) * t := by
  ring

/-- Every quadratic with nonzero leading coefficient admits a NONZERO modulus `N` such that
every multiple of `N` is a difference of two of its values. This is the whole engine. -/
theorem quad_diff_modulus (a b c : ℤ) (ha : a ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ t : ℤ, ∃ k l : ℤ,
      (a * k ^ 2 + b * k + c) - (a * l ^ 2 + b * l + c) = N * t := by
  by_cases hb : b = 0
  · -- `r = 1`: slope `4*a + 2*b = 4*a ≠ 0`.
    subst hb
    exact ⟨4 * a, mul_ne_zero (by norm_num) ha, fun t => ⟨t + 1, 1 - t, by ring⟩⟩
  · -- `r = 0`: slope `2*b ≠ 0`.
    exact ⟨2 * b, mul_ne_zero (by norm_num) hb, fun t => ⟨t, -t, by ring⟩⟩

/-! ### Stage 2 — the main theorem -/

/-- **Erdős 477, general quadratic rung.**
There is no `A ⊆ ℤ` such that every integer is UNIQUELY `α + f(k)` with `α ∈ A` and
`f(x) = a x² + b x + c`, for any `a ≠ 0` and any `b, c`.

Specialising `(a,b,c) = (1,0,0)` recovers the sealed `erdos477_no_square_tiling`
(see `erdos477_no_square_tiling_recovered` below). -/
theorem erdos477_no_quadratic_tiling (a b c : ℤ) (ha : a ≠ 0) :
    ¬ ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ,
      p.1 ∈ A ∧ (∃ k : ℤ, p.2 = a * k ^ 2 + b * k + c) ∧ n = p.1 + p.2 := by
  rintro ⟨A, hA⟩
  obtain ⟨N, hN, hrep⟩ := quad_diff_modulus a b c ha
  -- (i) distinct elements of `A` are incongruent mod `N`.
  have hdiff : ∀ α ∈ A, ∀ α' ∈ A, N ∣ (α - α') → α = α' := by
    intro α hα α' hα' hdvd
    obtain ⟨t, ht⟩ := hdvd
    obtain ⟨k, l, hkl⟩ := hrep t
    obtain ⟨p, -, huniq⟩ := hA (α + (a * l ^ 2 + b * l + c))
    have h1 : ((α, a * l ^ 2 + b * l + c) : ℤ × ℤ) = p :=
      huniq _ ⟨hα, ⟨l, rfl⟩, rfl⟩
    have h2 : ((α', a * k ^ 2 + b * k + c) : ℤ × ℤ) = p :=
      huniq _ ⟨hα', ⟨k, rfl⟩, by linarith⟩
    have h3 := congrArg Prod.fst (h1.trans h2.symm)
    simpa using h3
  -- (ii) hence `A` injects into `ℤ / |N|`, so it is finite.
  have hNabs : (0:ℤ) < |N| := abs_pos.mpr hN
  have hinj : Set.InjOn (fun x : ℤ => x % |N|) A := by
    intro x hx y hy hxy
    have hmod : Int.ModEq |N| x y := hxy
    have h1 : |N| ∣ (y - x) := Int.ModEq.dvd hmod
    have h2 : N ∣ (y - x) := (abs_dvd _ _).mp h1
    exact (hdiff y hy x hx h2).symm
  have hfin : A.Finite := by
    refine Set.Finite.of_finite_image ?_ hinj
    refine Set.Finite.subset (Set.finite_Ico (0:ℤ) |N|) ?_
    rintro z ⟨x, -, rfl⟩
    exact ⟨Int.emod_nonneg x (abs_ne_zero.mpr hN), Int.emod_lt_of_pos x hNabs⟩
  -- (iii) a finite `A` cannot cover, because `f(ℤ)` is bounded on one side.
  rcases (show a < 0 ∨ 0 < a by omega) with hneg | hpos
  · -- `a ≤ -1`: `f k ≤ c + b²`, and `A` is bounded above.
    obtain ⟨ub, hub⟩ := hfin.bddAbove
    obtain ⟨p, ⟨hpA, ⟨k, hk⟩, hn⟩, -⟩ := hA (ub + c + b ^ 2 + 1)
    have h1 : p.1 ≤ ub := hub hpA
    have h2 : p.2 ≤ c + b ^ 2 := by
      rw [hk]
      nlinarith [sq_nonneg (2 * k - b), sq_nonneg b,
        mul_nonneg (by linarith : (0:ℤ) ≤ -a - 1) (sq_nonneg k)]
    linarith
  · -- `a ≥ 1`: `f k ≥ c - b²`, and `A` is bounded below.
    obtain ⟨lb, hlb⟩ := hfin.bddBelow
    obtain ⟨p, ⟨hpA, ⟨k, hk⟩, hn⟩, -⟩ := hA (lb + c - b ^ 2 - 1)
    have h1 : lb ≤ p.1 := hlb hpA
    have h2 : c - b ^ 2 ≤ p.2 := by
      rw [hk]
      nlinarith [sq_nonneg (2 * k + b), sq_nonneg b,
        mul_nonneg (by linarith : (0:ℤ) ≤ a - 1) (sq_nonneg k)]
    linarith

/-! ### Stage 3 — faithfulness: the sealed theorem is the `(1,0,0)` instance -/

/-- The sealed `erdos477_no_square_tiling`, recovered verbatim as a corollary. This is the
check that the generalisation is faithful rather than a differently-shaped statement. -/
theorem erdos477_no_square_tiling_recovered :
    ¬ ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ,
      p.1 ∈ A ∧ (∃ k : ℤ, p.2 = k ^ 2) ∧ n = p.1 + p.2 := by
  have h := erdos477_no_quadratic_tiling 1 0 0 one_ne_zero
  simpa using h

/-- The `a ∣ b` variant asked for upstream (`erdos_477.variants.degree_two_dvd_condition_b_ne_zero`,
`sorry` in FormalConjectures) over `f(ℤ)`: strictly weaker than the theorem above, since neither
`a ∣ b` nor `b ≠ 0` is needed. Recorded to make the comparison mechanical. -/
theorem erdos477_no_quadratic_tiling_dvd (a b c : ℤ) (ha : a ≠ 0) (_hb : b ≠ 0) (_hab : a ∣ b) :
    ¬ ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ,
      p.1 ∈ A ∧ (∃ k : ℤ, p.2 = a * k ^ 2 + b * k + c) ∧ n = p.1 + p.2 :=
  erdos477_no_quadratic_tiling a b c ha

/-! ### Stage 4 — anti-vacuity gate

A negation is worthless if the shape it negates is unsatisfiable. `f(k) = 2k` (degree 1, so
outside Erdős 477's `deg ≥ 2` hypothesis) IS tiled, by `A = {0,1}`. So the `∃!` shape above
admits solutions, and the theorem is not winning on a broken quantifier. -/
theorem tiling_shape_is_satisfiable :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ,
      p.1 ∈ A ∧ (∃ k : ℤ, p.2 = 2 * k) ∧ n = p.1 + p.2 := by
  refine ⟨{0, 1}, fun n => ⟨(n % 2, 2 * (n / 2)), ⟨?_, ⟨n / 2, rfl⟩, ?_⟩, ?_⟩⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · dsimp only
    omega
  · rintro ⟨q1, q2⟩ ⟨hq1, ⟨k, hk⟩, hq⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq1
    dsimp only at hk hq
    subst hk
    simp only [Prod.mk.injEq]
    rcases hq1 with h | h <;> subst h <;> constructor <;> omega

/-! ### Stage 5 — the correction to OB1, kernel-checked

OB1 asserted the rung was "the same proof with `4` replaced by `4|a|`". The sealed proof's
engine is the pigeonhole `|A| ≤ 2`, obtained because every nonzero difference in `A - A` is
forced into ONE class mod 4, which is not closed under addition. That engine DIES at `a = 3`:
for `f(x) = 3x²` the difference set lies in `3ℤ`, so `±1` and `±2` are permitted differences
and `A = {0,1,2}` clears the whole difference obstruction. The pigeonhole gives nothing.

This is why the theorem above routes through a SUBGROUP (`quad_diff_identity`) instead. -/
theorem sealed_pigeonhole_fails_at_a_three (k l : ℤ) :
    (3 * k ^ 2 + 0 * k + 0) - (3 * l ^ 2 + 0 * l + 0) ≠ 1 ∧
    (3 * k ^ 2 + 0 * k + 0) - (3 * l ^ 2 + 0 * l + 0) ≠ 2 ∧
    (3 * k ^ 2 + 0 * k + 0) - (3 * l ^ 2 + 0 * l + 0) ≠ -1 ∧
    (3 * k ^ 2 + 0 * k + 0) - (3 * l ^ 2 + 0 * l + 0) ≠ -2 := by
  have h : (3 * k ^ 2 + 0 * k + 0) - (3 * l ^ 2 + 0 * l + 0) = 3 * (k ^ 2 - l ^ 2) := by ring
  rw [h]
  generalize k ^ 2 - l ^ 2 = m
  omega

end Erdos477Attack

#print axioms Erdos477Attack.quad_diff_identity
#print axioms Erdos477Attack.quad_diff_modulus
#print axioms Erdos477Attack.erdos477_no_quadratic_tiling
#print axioms Erdos477Attack.erdos477_no_square_tiling_recovered
#print axioms Erdos477Attack.erdos477_no_quadratic_tiling_dvd
#print axioms Erdos477Attack.tiling_shape_is_satisfiable
#print axioms Erdos477Attack.sealed_pigeonhole_fails_at_a_three
