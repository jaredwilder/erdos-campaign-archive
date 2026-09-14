import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def Powerful (n : ℕ) : Prop := ∀ (p : ℕ), p.Prime → p ∣ n → p * p ∣ n

def IsAP3 (a b c : ℕ) : Prop := a + c = b + b

def IsNondegenerateAP3 (a b c : ℕ) : Prop := IsAP3 a b c ∧ a < b ∧ b < c

open scoped Classical in
noncomputable def nthPowerful (k : ℕ) : ℕ :=
  sInf {n : ℕ | k < (Finset.filter (fun m => Powerful m) (Finset.range (n + 1))).card}

theorem msl_erdos938_b_m01_c3_triv : ∀ (k : ℕ), nthPowerful k < nthPowerful (k + 1) := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
