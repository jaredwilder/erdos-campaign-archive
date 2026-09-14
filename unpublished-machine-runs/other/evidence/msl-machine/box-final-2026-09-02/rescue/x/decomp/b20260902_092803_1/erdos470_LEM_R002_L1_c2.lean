import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def sigma (n : Nat) : Nat := ∑ d ∈ n.divisors, d

def pseudoperfect (n : Nat) : Prop :=
  ∃ s : Finset Nat, (∀ d ∈ s, d ∣ n ∧ d < n) ∧ ∑ d ∈ s, d = n

def weird (n : Nat) : Prop := 2 * n ≤ sigma n ∧ ¬ pseudoperfect n

def primWeird (n : Nat) : Prop :=
  weird n ∧ ∀ (m : Nat), m ∣ n → m < n → ¬ weird m

theorem msl_erdos470_lem_r002_l1_c2 (n : Nat) : primWeird n → weird n := by sorry
