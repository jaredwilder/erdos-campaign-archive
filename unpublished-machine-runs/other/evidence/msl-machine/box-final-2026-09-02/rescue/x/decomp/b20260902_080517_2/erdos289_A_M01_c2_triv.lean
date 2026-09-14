import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset

-- campaign vocabulary, already kernel-checked (msl_decompose)
def runSum (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n

def runProd (a b : ℕ) : ℕ := ∏ n ∈ Icc a b, n

def runNum (a b : ℕ) : ℕ := ∑ n ∈ Icc a b, runProd a b / n

-- proposed definitions

theorem msl_erdos289_a_m01_c2_triv (n : Nat) : 2 ≤ n → (n + 1) + 1 < n * (n + 1) := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
