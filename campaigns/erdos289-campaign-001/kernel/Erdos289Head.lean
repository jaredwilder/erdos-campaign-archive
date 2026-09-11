import Mathlib

/-!
Erdős 289, MSL round 2026-09-01.  Kernel targets, each an exact fragment.
  F1  : 1/2 + 1/3 + 1/4 > 1        (the run containing 2 is forced to be [2,3])
  F1' : 1 - (1/2 + 1/3) = 1/6       (the tail must sum to exactly 1/6)
  W4n : pure-ℕ form of "no run [a,b], 5 ≤ a < b ≤ 60, has reciprocal sum 1/6":
        with P = ∏ n and N = ∑ P/n over the run, 6·N ≠ P.   Kernel `decide`, Nat only.
  W4b : the bridge  runSum a b = N / P  in ℚ, so W4n is the ℚ statement.
-/

open Finset
set_option maxRecDepth 200000

def runSum (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n
def runProd (a b : ℕ) : ℕ := ∏ n ∈ Icc a b, n
def runNum (a b : ℕ) : ℕ := ∑ n ∈ Icc a b, runProd a b / n

theorem F1_head_forced : (1 : ℚ) / 2 + 1 / 3 + 1 / 4 > 1 := by norm_num
theorem F1_tail_value : (1 : ℚ) - (1 / 2 + 1 / 3) = 1 / 6 := by norm_num

theorem W4_nat_fragment :
    ∀ a ∈ Icc 5 60, ∀ b ∈ Icc (a + 1) 60, 6 * runNum a b ≠ runProd a b := by
  decide +kernel

theorem runProd_pos (a b : ℕ) (ha : 1 ≤ a) : 0 < runProd a b := by
  unfold runProd
  apply Finset.prod_pos
  intro n hn
  have := (Finset.mem_Icc.mp hn).1
  omega

theorem dvd_runProd (a b n : ℕ) (hn : n ∈ Icc a b) : n ∣ runProd a b :=
  Finset.dvd_prod_of_mem _ hn

theorem W4_bridge (a b : ℕ) (ha : 1 ≤ a) :
    runSum a b = (runNum a b : ℚ) / (runProd a b : ℚ) := by
  have hP : (runProd a b : ℚ) ≠ 0 := by
    exact_mod_cast (runProd_pos a b ha).ne'
  unfold runSum runNum
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hd := dvd_runProd a b n hn
  have hn0 : (n : ℚ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (show n ≠ 0 by omega)
  rw [Nat.cast_div hd hn0]
  field_simp

theorem W4_fragment :
    ∀ a ∈ Icc 5 60, ∀ b ∈ Icc (a + 1) 60, runSum a b ≠ 1 / 6 := by
  intro a ha b hb h
  have h5 : 1 ≤ a := by have := (Finset.mem_Icc.mp ha).1; omega
  rw [W4_bridge a b h5] at h
  have hP : (runProd a b : ℚ) ≠ 0 := by
    exact_mod_cast (runProd_pos a b h5).ne'
  have : (6 : ℚ) * runNum a b = runProd a b := by
    field_simp at h
    linarith
  have hnat : 6 * runNum a b = runProd a b := by exact_mod_cast this
  exact W4_nat_fragment a ha b hb hnat

#print axioms F1_head_forced
#print axioms F1_tail_value
#print axioms W4_nat_fragment
#print axioms W4_bridge
#print axioms W4_fragment
