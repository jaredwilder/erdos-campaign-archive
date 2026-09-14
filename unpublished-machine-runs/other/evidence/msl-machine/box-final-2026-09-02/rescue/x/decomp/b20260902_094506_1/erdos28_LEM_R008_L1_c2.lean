import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def reps (A : Set Nat) (n : Nat) : Nat :=
  ((Finset.Icc (0 : Nat) n).filter (fun (a : Nat) => a ∈ A ∧ (n - a) ∈ A)).card

theorem msl_erdos28_lem_r008_l1_c2 (r : Nat → Nat) : (∀ (N : Nat) (M : Nat), ∃ (n : Nat), M ≤ n ∧ r n ≥ N) → Filter.limsup (fun (n : Nat) => ((r n : Nat) : ℝ)) Filter.atTop = (⊤ : ℝ) := by sorry
