/-
# Erdős Problem 3 — sharpness of the density-transfer threshold

Companion to `Erdos3.lean`.

`Erdos3.summable_of_log_power_bound` shows that a counting bound `|A ∩ [0,N)| ≤ C·N/(log N)^{1+ε}`
with `ε > 0` forces `∑_{n ∈ A} 1/n < ∞`.  This file proves the threshold is SHARP: the
exponent `1 + ε` cannot be weakened to `1`.

The witness is the "critical set": in each dyadic block `[2^j, 2^{j+1})` keep the first
`⌊2^j/(j+1)⌋` integers.  Its dyadic densities are `≤ 1/(j+1)` — i.e. `≍ 1/log N` — yet its
reciprocal sum diverges.

CONSEQUENCE FOR THE PROBLEM.  Any attack on Erdős 3 through the counting function alone must
beat `N/log N` by a power of `log`.  Since the best unconditional bound for `k ≥ 4` progressions
(Gowers) is `N/(log log N)^{c_k}`, the gap that Erdős 3 asks to close is not a technicality:
it is quantified here, kernel-checked.

All results sorry-free.
-/

import Erdos3

open Finset Filter

namespace Erdos3

/-- `dcount j = ⌊2^j / (j+1)⌋` — how many integers the critical set keeps in block `j`. -/
def dcount (j : ℕ) : ℕ := 2 ^ j / (j + 1)

/-- The critical set: in the dyadic block `[2^j, 2^{j+1})` keep exactly the first
`dcount j = ⌊2^j/(j+1)⌋` integers. -/
def critical : Set ℕ := {n | n - 2 ^ (Nat.log 2 n) < dcount (Nat.log 2 n)}

lemma dcount_le (j : ℕ) : dcount j ≤ 2 ^ j := Nat.div_le_self _ _

lemma two_pow_succ (j : ℕ) : (2 : ℕ) ^ (j + 1) = 2 ^ j + 2 ^ j := by ring

lemma mem_critical_block {j i : ℕ} (h1 : 2 ^ j ≤ i) (h2 : i < 2 ^ (j + 1)) :
    i ∈ critical ↔ i < 2 ^ j + dcount j := by
  have hlog : Nat.log 2 i = j := Nat.log_eq_of_pow_le_of_lt_pow h1 h2
  show (i - 2 ^ (Nat.log 2 i) < dcount (Nat.log 2 i)) ↔ _
  rw [hlog]
  omega

/-- The critical set has exactly `⌊2^j/(j+1)⌋` elements in the dyadic block `j`. -/
lemma blockCount_critical (j : ℕ) : blockCount critical j = (dcount j : ℝ) := by
  have hd := dcount_le j
  have hsucc := two_pow_succ j
  have hle1 : (2 : ℕ) ^ j ≤ 2 ^ j + dcount j := Nat.le_add_right _ _
  have hle2 : (2 : ℕ) ^ j + dcount j ≤ 2 ^ (j + 1) := by omega
  unfold blockCount
  rw [← Finset.sum_Ico_consecutive (ind critical) hle1 hle2]
  have e1 : ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ j + dcount j), ind critical i = (dcount j : ℝ) := by
    have hall : ∀ i ∈ Finset.Ico (2 ^ j) (2 ^ j + dcount j), ind critical i = (1 : ℝ) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hup : i < 2 ^ (j + 1) := by omega
      have hmem : i ∈ critical := (mem_critical_block hi.1 hup).2 hi.2
      simp [ind, Set.indicator_of_mem hmem]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Ico]
    simp
  have e2 : ∑ i ∈ Finset.Ico (2 ^ j + dcount j) (2 ^ (j + 1)), ind critical i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    have h1 : 2 ^ j ≤ i := le_trans (Nat.le_add_right _ _) hi.1
    have hnot : i ∉ critical := by
      intro hmem
      have := (mem_critical_block h1 hi.2).1 hmem
      omega
    simp [ind, Set.indicator_of_notMem hnot]
  rw [e1, e2, add_zero]

/-- The dyadic densities of the critical set are at most `1/(j+1) ≍ 1/log N`. -/
theorem blockCount_critical_le (j : ℕ) :
    blockCount critical j / 2 ^ j ≤ 1 / ((j : ℝ) + 1) := by
  rw [blockCount_critical]
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hpow : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hnat : dcount j * (j + 1) ≤ 2 ^ j := by
    simpa [dcount] using Nat.div_mul_le_self (2 ^ j) (j + 1)
  have h1 : ((dcount j : ℕ) : ℝ) * ((j : ℝ) + 1) ≤ (2 : ℝ) ^ j := by exact_mod_cast hnat
  rw [div_le_div_iff₀ hpow hj]
  linarith

/-- Matching lower bound for the dyadic densities of the critical set. -/
theorem lower_bound (j : ℕ) :
    1 / ((j : ℝ) + 1) - ((1 : ℝ) / 2) ^ j ≤ blockCount critical j / 2 ^ j := by
  rw [blockCount_critical]
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hpow : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hmod : (j + 1) * (2 ^ j / (j + 1)) + 2 ^ j % (j + 1) = 2 ^ j := Nat.div_add_mod _ _
  have hlt : 2 ^ j % (j + 1) < j + 1 := Nat.mod_lt _ (Nat.succ_pos j)
  have hR : (((j + 1) * dcount j + 2 ^ j % (j + 1) : ℕ) : ℝ) = ((2 ^ j : ℕ) : ℝ) := by
    rw [show (j + 1) * dcount j + 2 ^ j % (j + 1) = 2 ^ j from hmod]
  push_cast at hR
  have hltR : (((2 ^ j % (j + 1) : ℕ)) : ℝ) < (j : ℝ) + 1 := by exact_mod_cast hlt
  have hmodnn : (0 : ℝ) ≤ (((2 ^ j % (j + 1) : ℕ)) : ℝ) := by positivity
  have key : (2 : ℝ) ^ j ≤ ((dcount j : ℝ) + 1) * ((j : ℝ) + 1) := by nlinarith [hR, hltR]
  rw [le_div_iff₀ hpow]
  have h12 : ((1 : ℝ) / 2) ^ j = 1 / (2 : ℝ) ^ j := by rw [div_pow, one_pow]
  rw [h12]
  have expand : (1 / ((j : ℝ) + 1) - 1 / (2 : ℝ) ^ j) * (2 : ℝ) ^ j
      = (2 : ℝ) ^ j / ((j : ℝ) + 1) - 1 := by
    field_simp
  rw [expand, sub_le_iff_le_add, div_le_iff₀ hj]
  nlinarith [key]

/-- **The critical set has a divergent reciprocal sum.** -/
theorem not_summable_critical : ¬ Summable (recip critical) := by
  rw [summable_recip_iff]
  intro hs
  have hgeo : Summable fun j : ℕ => ((1 : ℝ) / 2) ^ j :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hnn : ∀ j : ℕ, 0 ≤ 1 / ((j : ℝ) + 1) - ((1 : ℝ) / 2) ^ j := by
    intro j
    have hjlt : (j : ℕ) < 2 ^ j := Nat.lt_two_pow_self
    have h1 : ((j : ℝ)) + 1 ≤ (2 : ℝ) ^ j := by
      have : ((j : ℕ) : ℝ) + 1 ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hjlt
      simpa using this
    have h12 : ((1 : ℝ) / 2) ^ j = 1 / (2 : ℝ) ^ j := by rw [div_pow, one_pow]
    rw [h12, sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) h1
  have hsub : Summable fun j : ℕ => 1 / ((j : ℝ) + 1) - ((1 : ℝ) / 2) ^ j :=
    Summable.of_nonneg_of_le hnn (fun j => lower_bound j) hs
  have hharm : Summable fun j : ℕ => 1 / ((j : ℝ) + 1) := by
    have := hsub.add hgeo
    simpa using this
  have h' : Summable fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) := by push_cast; exact hharm
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).1 h')

/-- **Sharpness of the density-transfer threshold.**  There is a set of naturals whose
reciprocal sum diverges even though its dyadic densities decay like `1/j ≍ 1/log N`.

By `Erdos3.summable_recip_iff` the dyadic density series is an exact reformulation of the
hypothesis of Erdős Problem 3, so this says: the exponent `1 + ε` in
`Erdos3.summable_of_log_power_bound` cannot be lowered to `1`.  Any counting-function route to
Erdős 3 must beat `N/log N` by a positive power of `log N`. -/
theorem log_power_threshold_sharp :
    ∃ A : Set ℕ, ¬ Summable (recip A) ∧
      (∀ j : ℕ, blockCount A j / 2 ^ j ≤ 1 / ((j : ℝ) + 1)) :=
  ⟨critical, not_summable_critical, blockCount_critical_le⟩

/-- The same statement in subtype form, matching the shape of the FormalConjectures
hypothesis `¬ Summable fun a : A ↦ 1/a`. -/
theorem log_power_threshold_sharp' :
    ∃ A : Set ℕ, (¬ Summable fun a : A => 1 / (a : ℝ)) ∧
      (∀ j : ℕ, blockCount A j / 2 ^ j ≤ 1 / ((j : ℝ) + 1)) :=
  ⟨critical, fun h => not_summable_critical ((summable_subtype_iff critical).1 h),
    blockCount_critical_le⟩

end Erdos3
