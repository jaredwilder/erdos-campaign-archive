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
set_option maxHeartbeats 400000

-- THE NORMALIZATION PRELUDE (msl_ladder, deterministic, $0).
-- The claim it tests: most leaf failures on an arithmetic DAG are SIDE-CONDITIONS
-- (an un-introduced hypothesis, a numeric coercion, a nonnegativity obligation),
-- not mathematics.  Each step is `try`, so the prelude never fails and never
-- changes what a tactic after it is allowed to prove.
macro "msl_prelude" : tactic =>
  `(tactic| ((try intros); (try push_cast); (try positivity)))

theorem runSum_char_over_Q (a b : ℕ) (ha : 1 ≤ a) (q : ℚ) : ∀ (a b : ℕ), 1 ≤ a → ∀ (q : ℚ), runSum a b = q ↔ (runProd a b : ℚ) * q = (runNum a b : ℚ) := by
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

#print axioms runSum_char_over_Q
