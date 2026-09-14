import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Classical

/-- `unitPairCount S` is the number of unordered pairs of distinct points of `S` at
distance exactly `1`; each unordered pair occurs twice among ordered pairs, hence the
halving. -/
noncomputable def unitPairCount {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  ((S ×ˢ S).filter fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      p.1 ≠ p.2 ∧ dist p.1 p.2 = (1 : ℝ)).card / (2 : ℕ)

/-- `IsMaxUnitPairs d n k` is the typed form of `f_d(n) = k` for the frozen contract
root: every `n`-point subset of `ℝ^d` spans at most `k` unit-distance pairs, and some
`n`-point subset spans exactly `k`; since `unitPairCount` is bounded by
`n * (n - 1) / 2`, this holds exactly when `k` is the minimal such universal bound. -/
def IsMaxUnitPairs (d n k : ℕ) : Prop :=
  (∀ S : Finset (EuclideanSpace ℝ (Fin d)), S.card = n → unitPairCount S ≤ k) ∧
  ∃ S : Finset (EuclideanSpace ℝ (Fin d)), S.card = n ∧ unitPairCount S = k

theorem msl_erdos1085_lem_r006_l1_c1 (d : ℕ) (hd : (1 : ℕ) ≤ d) : IsMaxUnitPairs d (0 : ℕ) (0 : ℕ) ∧ IsMaxUnitPairs d (1 : ℕ) (0 : ℕ) ∧ IsMaxUnitPairs d (2 : ℕ) (1 : ℕ) := by sorry
