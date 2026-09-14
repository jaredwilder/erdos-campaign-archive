import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def sigma (n : Nat) : Nat := ∑ d ∈ n.divisors, d

def pseudoperfect (n : Nat) : Prop :=
  ∃ s : Finset Nat, (∀ d ∈ s, d ∣ n ∧ d < n) ∧ ∑ d ∈ s, d = n

def weird (n : Nat) : Prop := 2 * n ≤ sigma n ∧ ¬ pseudoperfect n

def primWeird (n : Nat) : Prop :=
  weird n ∧ ∀ (m : Nat), m ∣ n → m < n → ¬ weird m

theorem msl_erdos470_lem_r002_l1_composition : ((∀ (k : Nat), ∃ (n : Nat), k < n ∧ Odd n ∧ primWeird n) ∧ (∀ (n : Nat), primWeird n → weird n)) → (∀ (k : Nat), ∃ (n : Nat), k < n ∧ Odd n ∧ weird n) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos470_lem_r002_l1_composition
