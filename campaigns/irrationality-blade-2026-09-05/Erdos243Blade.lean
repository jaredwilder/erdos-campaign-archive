/-
Erdos 243 instantiation of the irrationality blade — supporting lemmas.
-/
import Mathlib

namespace Erdos243Blade

open Finset

/-- A divisibility chain divides forward. -/
theorem dvd_of_le (a : ℕ → ℕ) (hdvd : ∀ m, a m ∣ a (m + 1)) :
    ∀ j m, j ≤ m → a j ∣ a m := by
  intro j m hjm
  induction m with
  | zero =>
    have hj : j = 0 := Nat.le_zero.mp hjm
    rw [hj]
  | succ n ih =>
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · exact dvd_trans (ih (Nat.lt_succ_iff.mp h)) (hdvd n)
    · have hj : j = n + 1 := le_antisymm hjm h
      rw [hj]

/-- The head-clearing multiplier: `a m` clears the denominators of the first `m+1` terms. -/
theorem head_integral (a : ℕ → ℕ) (hpos : ∀ m, 0 < a m) (hdvd : ∀ m, a m ∣ a (m + 1)) (m : ℕ) :
    (a m : ℝ) * (∑ j ∈ range (m + 1), (1 : ℝ) / (a j))
      = ((∑ j ∈ range (m + 1), a m / a j : ℕ) : ℝ) := by
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hd : a j ∣ a m := dvd_of_le a hdvd j m hjm
  have hne : ((a j : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (hpos j).ne'
  rw [Nat.cast_div hd hne]
  ring

/-- Doubling from a point forces geometric growth. -/
theorem geometric_growth (a : ℕ → ℕ) (M : ℕ) (hgrow : ∀ m, M ≤ m → 2 * a m ≤ a (m + 1)) :
    ∀ i, 2 ^ i * a M ≤ a (M + i) := by
  intro i
  induction i with
  | zero => simp
  | succ n ih =>
    have h1 : 2 * a (M + n) ≤ a (M + n + 1) := hgrow (M + n) (Nat.le_add_right M n)
    calc 2 ^ (n + 1) * a M = 2 * (2 ^ n * a M) := by ring
      _ ≤ 2 * a (M + n) := by omega
      _ ≤ a (M + n + 1) := h1
      _ = a (M + (n + 1)) := by ring_nf

/-- Termwise geometric domination from the doubling point. -/
theorem term_bound (a : ℕ → ℕ) (hpos : ∀ m, 0 < a m) (M : ℕ)
    (hgrow : ∀ m, M ≤ m → 2 * a m ≤ a (m + 1)) (i : ℕ) :
    (1 : ℝ) / (a (M + i)) ≤ ((1 : ℝ) / 2) ^ i * (1 / (a M)) := by
  have hg : 2 ^ i * a M ≤ a (M + i) := geometric_growth a M hgrow i
  have hgR : ((2 : ℝ) ^ i) * (a M : ℝ) ≤ (a (M + i) : ℝ) := by exact_mod_cast hg
  have hM : (0 : ℝ) < (a M : ℝ) := by exact_mod_cast hpos M
  have hden : (0 : ℝ) < (2 : ℝ) ^ i * (a M : ℝ) := by positivity
  calc (1 : ℝ) / (a (M + i)) ≤ 1 / ((2 : ℝ) ^ i * (a M : ℝ)) :=
        one_div_le_one_div_of_le hden hgR
    _ = ((1 : ℝ) / 2) ^ i * (1 / (a M : ℝ)) := by
        rw [div_pow, one_pow]; field_simp

/-- The finite tail is bounded by twice the reciprocal of its first denominator. -/
theorem finite_tail_bound (a : ℕ → ℕ) (hpos : ∀ m, 0 < a m) (M : ℕ)
    (hgrow : ∀ m, M ≤ m → 2 * a m ≤ a (m + 1)) (n : ℕ) :
    ∑ i ∈ range n, (1 : ℝ) / (a (M + i)) ≤ 2 / (a M) := by
  have hM : (0 : ℝ) < (a M : ℝ) := by exact_mod_cast hpos M
  have hinv : (0 : ℝ) ≤ 1 / (a M : ℝ) := by positivity
  calc ∑ i ∈ range n, (1 : ℝ) / (a (M + i))
      ≤ ∑ i ∈ range n, ((1 : ℝ) / 2) ^ i * (1 / (a M : ℝ)) :=
        Finset.sum_le_sum fun i _ => term_bound a hpos M hgrow i
    _ = (∑ i ∈ range n, ((1 : ℝ) / 2) ^ i) * (1 / (a M : ℝ)) := by rw [← Finset.sum_mul]
    _ ≤ 2 * (1 / (a M : ℝ)) := mul_le_mul_of_nonneg_right (sum_geometric_two_le n) hinv
    _ = 2 / (a M : ℝ) := by ring

end Erdos243Blade

#print axioms Erdos243Blade.dvd_of_le
#print axioms Erdos243Blade.head_integral
#print axioms Erdos243Blade.geometric_growth
#print axioms Erdos243Blade.term_bound
#print axioms Erdos243Blade.finite_tail_bound
