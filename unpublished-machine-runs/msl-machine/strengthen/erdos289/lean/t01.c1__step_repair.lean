import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset

-- campaign vocabulary, already kernel-checked (msl_decompose)
def runSum (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n

def runProd (a b : ℕ) : ℕ := ∏ n ∈ Icc a b, n

def runNum (a b : ℕ) : ℕ := ∑ n ∈ Icc a b, runProd a b / n

-- proposed definitions

abbrev msl_p_erdos289_a_m01_d1 (n : Nat) : Prop :=
  2 ≤ n → ((1 : ℚ) / n = (1 : ℚ) / (n + 1) + (1 : ℚ) / (n * (n + 1)))

abbrev msl_q_erdos289_a_m01_d1_s1 (n : Nat) : Prop :=
  (2 ≤ n → (∑ i ∈ Finset.Icc 2 n, (1 : ℚ) / (i * (i - 1)) = (1 : ℚ) - (1 : ℚ) / n))
theorem th_t01_c1_step : ∀ (k : Nat), msl_q_erdos289_a_m01_d1_s1 k → msl_q_erdos289_a_m01_d1_s1 (k + 1) := by
  intro k h
  try simp only [msl_q_erdos289_a_m01_d1_s1, msl_p_erdos289_a_m01_d1] at *
  intro k ih
  rcases k with _ | _ | k
  · show (∑ i ∈ Finset.Icc 2 1, (1:ℚ)/(i*(i-1))) = (1:ℚ) - 1/1
    simp [Finset.Icc_eq_empty_iff] <;> norm_num
  · show (∑ i ∈ Finset.Icc 2 2, (1:ℚ)/(i*(i-1))) = (1:ℚ) - 1/2
    simp only [Finset.Icc_self, Finset.sum_singleton]
    norm_num
  · show (∑ i ∈ Finset.Icc 2 (k+2+1), (1:ℚ)/(i*(i-1))) = (1:ℚ) - 1/(k+2+1)
    have hle : (2:ℕ) ≤ k + 2 := by omega
    have htop : (2:ℕ) ≤ k + 2 + 1 := by omega
    rw [Finset.sum_Icc_succ_top htop, ih hle]
    have hsub : ((k + 2 + 1 : ℕ) - 1) = k + 2 := by omega
    rw [hsub]
    have h1 : (k + 2 : ℚ) ≠ 0 := by exact_mod_cast (by omega : (k + 2 : ℕ) ≠ 0)
    have h3 : (k + 2 + 1 : ℚ) ≠ 0 := by exact_mod_cast (by omega : (k + 2 + 1 : ℕ) ≠ 0)
    have key : (1:ℚ)/((k+2+1)*(k+2)) = 1/(k+2) - 1/(k+2+1) := by
      field_simp
    rw [key]
    ring

#print axioms th_t01_c1_step
