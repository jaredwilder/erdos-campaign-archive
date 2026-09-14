import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def gk (k n : Nat) : Int :=
  sSup {v : Int | ∃ a : Fin k → Nat, (∀ i : Fin k, 1 ≤ a i) ∧
    ((∏ i : Fin k, (a i).factorial) ∣ n.factorial) ∧
    v = (∑ i : Fin k, ((a i : Nat) : Int)) - (n : Int)}

theorem msl_erdos400_a_m05_c1 (k : Nat) : 2 ≤ k → ∃ c : ℝ, Filter.Tendsto (fun x : Nat => ((∑ n ∈ Finset.Icc 1 x, ((gk k n : Int) : ℝ)) : ℝ) / ((x : ℝ) * Real.log (x : ℝ))) Filter.atTop (nhds c) := by sorry
