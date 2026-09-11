/-
# Erdős Problem 3 — sharpness, in counting-function form

Companion to `Erdos3.lean` and `Erdos3Sharp.lean`.

`Erdos3.summable_of_log_power_bound` :  `count A N ≤ C·N/(log N)^{1+ε}` eventually, `ε > 0`
                                        ⟹ `∑_{n ∈ A} 1/n < ∞`.

This file proves the exact converse boundary in the SAME language: the critical set of
`Erdos3Sharp` satisfies `count A N ≤ 1 + (4 log 2)·N / log N` for all `N ≥ 4`, and yet
`∑_{n ∈ A} 1/n = ∞`.

So the two theorems bracket the threshold at exactly `(log N)^1`:

  * exponent `> 1`  ⟹  convergence   (`Erdos3.summable_of_log_power_bound`)
  * exponent `= 1`  ⟹  no conclusion (`Erdos3.log_threshold_sharp_counting`, below)

All results sorry-free.
-/

import Erdos3Sharp

open Finset Filter

namespace Erdos3

lemma count_mono (A : Set ℕ) {M N : ℕ} (h : M ≤ N) : count A M ≤ count A N := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ind_nonneg A i)
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega

/-- The dyadic decomposition, for an arbitrary summand. -/
lemma dyadic_split_gen (f : ℕ → ℝ) : ∀ J : ℕ,
    ∑ i ∈ Ico 1 (2 ^ J), f i = ∑ j ∈ range J, ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)), f i := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
      have h1 : (1 : ℕ) ≤ 2 ^ J := Nat.one_le_two_pow
      have h2 : (2 : ℕ) ^ J ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)
      rw [Finset.sum_range_succ, ← ih, ← Finset.sum_Ico_consecutive f h1 h2]

lemma count_two_pow (A : Set ℕ) (J : ℕ) :
    count A (2 ^ J) = ind A 0 + ∑ j ∈ range J, blockCount A j := by
  unfold count blockCount
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (ind A) (Nat.zero_le 1) (Nat.one_le_two_pow),
    dyadic_split_gen (ind A) J]
  simp

lemma count_critical_two_pow (J : ℕ) :
    count critical (2 ^ J) = 1 + ∑ j ∈ range J, (dcount j : ℝ) := by
  rw [count_two_pow]
  congr 1
  · have h0 : (0 : ℕ) ∈ critical := by
      show (0 - 2 ^ (Nat.log 2 0) < dcount (Nat.log 2 0))
      simp [dcount, Nat.log_zero_right]
    simp [ind, Set.indicator_of_mem h0]
  · exact Finset.sum_congr rfl fun j _ => blockCount_critical j

/-- `∑_{j<J} 2^j/(j+1) ≤ 2^{J+1}/J` for `J ≥ 2`.  The series is dominated by its last term,
which is what makes the critical set have counting function `≍ N/log N`. -/
lemma geom_over_linear (J : ℕ) (hJ : 2 ≤ J) :
    ∑ j ∈ range J, (2 : ℝ) ^ j / ((j : ℝ) + 1) ≤ (2 : ℝ) ^ (J + 1) / (J : ℝ) := by
  induction J, hJ using Nat.le_induction with
  | base => norm_num [Finset.sum_range_succ]
  | succ J hJ ih =>
      rw [Finset.sum_range_succ]
      push_cast
      have hJpos : (0 : ℝ) < (J : ℝ) := by
        have : (0 : ℕ) < J := by omega
        exact_mod_cast this
      have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by linarith
      have hJ2R : (2 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
      have hpow : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
      have hstep : (2 : ℝ) ^ (J + 1) / (J : ℝ) + (2 : ℝ) ^ J / ((J : ℝ) + 1)
          ≤ (2 : ℝ) ^ (J + 1 + 1) / ((J : ℝ) + 1) := by
        rw [div_add_div _ _ (ne_of_gt hJpos) (ne_of_gt hJ1),
          div_le_div_iff₀ (by positivity) hJ1]
        have e1 : (2 : ℝ) ^ (J + 1) = 2 * 2 ^ J := by ring
        have e2 : (2 : ℝ) ^ (J + 1 + 1) = 4 * 2 ^ J := by ring
        rw [e1, e2]
        nlinarith [mul_nonneg (mul_nonneg hpow.le hJ1.le) (by linarith : (0 : ℝ) ≤ (J : ℝ) - 2)]
      linarith [ih]

lemma count_critical_two_pow_le (J : ℕ) (hJ : 2 ≤ J) :
    count critical (2 ^ J) ≤ 1 + (2 : ℝ) ^ (J + 1) / (J : ℝ) := by
  rw [count_critical_two_pow]
  have h1 : ∑ j ∈ range J, (dcount j : ℝ) ≤ ∑ j ∈ range J, (2 : ℝ) ^ j / ((j : ℝ) + 1) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hnat : dcount j * (j + 1) ≤ 2 ^ j := by
      simpa [dcount] using Nat.div_mul_le_self (2 ^ j) (j + 1)
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hj1]
    exact_mod_cast hnat
  linarith [geom_over_linear J hJ]

/-- **The counting function of the critical set is `≤ 1 + (4 log 2)·N / log N`.** -/
theorem count_critical_le (N : ℕ) (hN : 4 ≤ N) :
    count critical N ≤ 1 + 4 * Real.log 2 * (N : ℝ) / Real.log N := by
  set J := Nat.log 2 N with hJdef
  have hlow : 2 ^ J ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hhigh : N < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hJ2 : 2 ≤ J := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hmono : count critical N ≤ count critical (2 ^ (J + 1)) :=
    count_mono critical (le_of_lt hhigh)
  have hb := count_critical_two_pow_le (J + 1) (by omega)
  push_cast at hb
  have hlogN : 0 < Real.log N := by
    apply Real.log_pos
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJ1pos : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have hNR : (2 : ℝ) ^ J ≤ (N : ℝ) := by exact_mod_cast hlow
  have hlogbound : Real.log N < ((J : ℝ) + 1) * Real.log 2 := by
    have h1 : (N : ℝ) < (2 : ℝ) ^ (J + 1) := by exact_mod_cast hhigh
    have h2 := Real.log_lt_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hkey : (2 : ℝ) ^ (J + 1 + 1) / ((J : ℝ) + 1)
      ≤ 4 * Real.log 2 * (N : ℝ) / Real.log N := by
    have e : (2 : ℝ) ^ (J + 1 + 1) = 4 * 2 ^ J := by ring
    rw [e, div_le_div_iff₀ hJ1pos hlogN]
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (0 : ℕ) < N := by omega
      exact_mod_cast this
    nlinarith [mul_le_mul_of_nonneg_right hNR (le_of_lt hlogN),
      mul_lt_mul_of_pos_left hlogbound hNpos]
  linarith [hmono, hb, hkey]

/-- **Sharpness of the density-transfer threshold, in counting-function form.**

There is a set `A ⊆ ℕ` with `count A N ≤ 1 + C·N/log N` for all `N ≥ 4` whose reciprocal sum
still diverges.  Together with `Erdos3.summable_of_log_power_bound` this pins the threshold
for Erdős Problem 3 at exactly one power of `log`:  a counting bound with `(log N)^{1+ε}`
settles the problem, a counting bound with `(log N)^1` says nothing. -/
theorem log_threshold_sharp_counting :
    ∃ (A : Set ℕ) (C : ℝ), 0 ≤ C ∧ (¬ Summable fun a : A => 1 / (a : ℝ)) ∧
      ∀ N : ℕ, 4 ≤ N → count A N ≤ 1 + C * (N : ℝ) / Real.log N := by
  refine ⟨critical, 4 * Real.log 2, ?_, ?_, ?_⟩
  · have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    linarith
  · exact fun h => not_summable_critical ((summable_subtype_iff critical).1 h)
  · intro N hN
    have := count_critical_le N hN
    calc count critical N ≤ 1 + 4 * Real.log 2 * (N : ℝ) / Real.log N := this
      _ = 1 + 4 * Real.log 2 * (N : ℝ) / Real.log N := rfl

end Erdos3
