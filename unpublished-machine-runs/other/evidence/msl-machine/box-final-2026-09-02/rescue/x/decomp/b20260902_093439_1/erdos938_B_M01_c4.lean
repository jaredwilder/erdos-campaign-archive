import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def Powerful (n : ℕ) : Prop := ∀ (p : ℕ), p.Prime → p ∣ n → p * p ∣ n

def IsAP3 (a b c : ℕ) : Prop := a + c = b + b

def IsNondegenerateAP3 (a b c : ℕ) : Prop := IsAP3 a b c ∧ a < b ∧ b < c

open scoped Classical in
noncomputable def nthPowerful (k : ℕ) : ℕ :=
  sInf {n : ℕ | k < (Finset.filter (fun m => Powerful m) (Finset.range (n + 1))).card}

theorem msl_erdos938_b_m01_c4 : ¬{P : Finset ℕ | ∃ (k : ℕ), P = ({nthPowerful k, nthPowerful (k + 1), nthPowerful (k + 2)} : Finset ℕ) ∧
  IsNondegenerateAP3 (nthPowerful k) (nthPowerful (k + 1)) (nthPowerful (k + 2))}.Finite := by sorry
