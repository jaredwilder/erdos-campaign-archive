import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset

-- campaign vocabulary, already kernel-checked (msl_decompose)
def runSum (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n

def runProd (a b : ℕ) : ℕ := ∏ n ∈ Icc a b, n

def runNum (a b : ℕ) : ℕ := ∑ n ∈ Icc a b, runProd a b / n

-- proposed definitions
set_option maxHeartbeats 400000

-- THE NORMALIZATION PRELUDE (msl_ladder, deterministic, $0).
-- The claim it tests: most leaf failures on an arithmetic DAG are SIDE-CONDITIONS
-- (an un-introduced hypothesis, a numeric coercion, a nonnegativity obligation),
-- not mathematics.  Each step is `try`, so the prelude never fails and never
-- changes what a tactic after it is allowed to prove.
macro "msl_prelude" : tactic =>
  `(tactic| ((try intros); (try push_cast); (try positivity)))

theorem msl_erdos289_a_m01_c1 (n : Nat) : 2 ≤ n → ((1 : ℚ) / n = (1 : ℚ) / (n + 1) + (1 : ℚ) / (n * (n + 1))) := by
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
  | (intros; have hzq_n : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); have hsq_n : ((n : ℚ) + 1) ≠ 0 := by positivity; field_simp; done)
  | (intros; have hzq_n : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); have hsq_n : ((n : ℚ) + 1) ≠ 0 := by positivity; field_simp; ring; done)
  | (intros; have hzq_n : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); have hsq_n : ((n : ℚ) + 1) ≠ 0 := by positivity; push_cast; done)
  | (intros; have hzq_n : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); have hsq_n : ((n : ℚ) + 1) ≠ 0 := by positivity; push_cast; field_simp; done)
  | (intros; have hzq_n : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); have hsq_n : ((n : ℚ) + 1) ≠ 0 := by positivity; push_cast; field_simp; ring; done)
  | (intros; have hzq_n : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); have hsq_n : ((n : ℚ) + 1) ≠ 0 := by positivity; field_simp; linarith; done)

#print axioms msl_erdos289_a_m01_c1
