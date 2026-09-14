import Mathlib
open Finset
set_option autoImplicit false
/-!
Erdős 289, MSL round 2026-09-01.  Kernel targets, each an exact fragment.
  F1  : 1/2 + 1/3 + 1/4 > 1        (the run containing 2 is forced to be [2,3])
  F1' : 1 - (1/2 + 1/3) = 1/6       (the tail must sum to exactly 1/6)
  W4n : pure-ℕ form of "no run [a,b], 5 ≤ a < b ≤ 60, has reciprocal sum 1/6":
        with P = ∏ n and N = ∑ P/n over the run, 6·N ≠ P.   Kernel `decide`, Nat only.
  W4b : the bridge  runSum a b = N / P  in ℚ, so W4n is the ℚ statement.
-/
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
  have hd := dvd_runProd a b n hn
  have hn0 : (n : ℚ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  rw [Nat.cast_div hd hn0]
  field_simp
set_option maxHeartbeats 400000

-- THE NORMALIZATION PRELUDE (msl_ladder, deterministic, $0).
-- The claim it tests: most leaf failures on an arithmetic DAG are SIDE-CONDITIONS
-- (an un-introduced hypothesis, a numeric coercion, a nonnegativity obligation),
-- not mathematics.  Each step is `try`, so the prelude never fails and never
-- changes what a tactic after it is allowed to prove.
macro "msl_prelude" : tactic =>
  `(tactic| ((try intros); (try push_cast); (try positivity)))

-- ---- children, INCLUDED BY SOURCE (each already PROVED_KERNEL alone)
theorem runProd_pos (a b : ℕ) (ha : 1 ≤ a) : 0 < runProd a b := by
  first
  | decide
  | norm_num
  | simp

theorem W4_bridge (a b : ℕ) (ha : 1 ≤ a) : runSum a b = (runNum a b : ℚ) / (runProd a b : ℚ) := by
  first
  | decide
  | norm_num
  | simp

theorem F1_tail_value (1 : ℚ) - (1 / 2 + 1 / 3) = 1 / 6 := by
  first
  | decide
  | norm_num
  | simp

theorem W4_nat_fragment ∀ a ∈ Icc 5 60, ∀ b ∈ Icc (a + 1) 60, 6 * runNum a b ≠ runProd a b := by
  first
  | decide
  | norm_num
  | simp

theorem F1_head_forced (1 : ℚ) / 2 + 1 / 3 + 1 / 4 > 1 := by
  first
  | decide
  | norm_num
  | simp

theorem dvd_runProd (a b n : ℕ) (hn : n ∈ Icc a b) : n ∣ runProd a b := by
  first
  | decide
  | norm_num
  | simp

theorem W4_fragment ∀ a ∈ Icc 5 60, ∀ b ∈ Icc (a + 1) 60, runSum a b ≠ 1 / 6 := by
  first
  | decide
  | norm_num
  | simp

-- ---- the composition: children -> parent
theorem W4_two_interval_fragment_composition : ((runProd_pos : ($v0 $v1 : ℕ) (ha : 1 ≤ $v0) : 0 < runProd $v0 $v1) ∧ (W4_bridge : ($v0 $v1 : ℕ) (ha : 1 ≤ $v0) : runSum $v0 $v1 = (runNum $v0 $v1 : ℚ) / (runProd $v0 $v1 : ℚ)) ∧ (F1_tail_value : (1 : ℚ) - (1 / 2 + 1 / 3) = 1 / 6) ∧ (W4_nat_fragment : ∀ $v0 ∈ Icc 5 60, ∀ $v1 ∈ Icc ($v0 + 1) 60, 6 * runNum $v0 $v1 ≠ runProd $v0 $v1) ∧ (F1_head_forced : (1 : ℚ) / 2 + 1 / 3 + 1 / 4 > 1) ∧ (dvd_runProd : ($v0 $v1 $v2 : ℕ) (hn : $v2 ∈ Icc $v0 $v1) : $v2 ∣ runProd $v0 $v1) ∧ (W4_fragment : ∀ $v0 ∈ Icc 5 60, ∀ $v1 ∈ Icc ($v0 + 1) 60, runSum $v0 $v1 ≠ 1 / 6)) → (theorem W4_two_interval_fragment : ∀ a ∈ Finset.Icc 5 60, ∀ b ∈ Finset.Icc (a + 1) 60, ∀ c ∈ Finset.Icc (b + 2) 60, ∀ d ∈ Finset.Icc (c + 1) 60, runSum a b + runSum c d ≠ (1 : ℚ) / 6) := by
  first
  | (decide; done)
  | (omega; done)
  | (norm_num; done)
  | (ring_nf; done)
  | (ring_nf; ring; done)
  | (linarith; done)
  | (nlinarith; done)
  | (positivity; done)
  | (gcongr; done)
  | (simp_all; done)
  | (aesop; done)
  | (msl_prelude; done)
  | (msl_prelude; omega; done)
  | (msl_prelude; norm_num; done)
  | (msl_prelude; linarith; done)
  | (msl_prelude; nlinarith; done)
  | (msl_prelude; ring_nf; done)
  | (msl_prelude; ring_nf; ring; done)
  | (msl_prelude; decide; done)
  | (msl_prelude; simp_all; done)
  | (msl_prelude; aesop; done)
  | (msl_prelude; field_simp; done)
  | (msl_prelude; field_simp; ring; done)
  | (msl_prelude; qify; omega; done)

-- ---- the parent, by exact application of the composition
theorem W4_two_interval_fragment : theorem W4_two_interval_fragment : ∀ a ∈ Finset.Icc 5 60, ∀ b ∈ Finset.Icc (a + 1) 60, ∀ c ∈ Finset.Icc (b + 2) 60, ∀ d ∈ Finset.Icc (c + 1) 60, runSum a b + runSum c d ≠ (1 : ℚ) / 6 := by
  first
  | exact W4_two_interval_fragment_composition ⟨runProd_pos, W4_bridge, F1_tail_value, W4_nat_fragment, F1_head_forced, dvd_runProd, W4_fragment⟩
  | (apply W4_two_interval_fragment_composition; exact ⟨runProd_pos, W4_bridge, F1_tail_value, W4_nat_fragment, F1_head_forced, dvd_runProd, W4_fragment⟩)
  | (intros; exact W4_two_interval_fragment_composition ⟨runProd_pos, W4_bridge, F1_tail_value, W4_nat_fragment, F1_head_forced, dvd_runProd, W4_fragment⟩)

#print axioms W4_two_interval_fragment_composition
#print axioms W4_two_interval_fragment
