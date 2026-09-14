import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open scoped Real

noncomputable def sqrtN (n : Nat) : ℝ := (n : ℝ) ^ ((1 : ℝ) / 2)

noncomputable def root4N (n : Nat) : ℝ := (n : ℝ) ^ ((1 : ℝ) / 4)

noncomputable def divisorsInWindow (n : Nat) (C : ℝ) : Finset Nat :=
  (Nat.divisors n).filter (fun (d : Nat) =>
    sqrtN n < (d : ℝ) ∧ (d : ℝ) ≤ sqrtN n + C * root4N n)

noncomputable def divisorsBelowWindow (n : Nat) (C : ℝ) : Finset Nat :=
  (Nat.divisors n).filter (fun (e : Nat) =>
    sqrtN n - C * root4N n ≤ (e : ℝ) ∧ (e : ℝ) < sqrtN n)

theorem msl_erdos887_lem_r006_r006_parent : ∃ (K : Nat), ∀ (C : ℝ), C > 0 → ∃ (N : Nat), ∀ (n : Nat), n ≥ N → (divisorsInWindow n C).card ≤ K := by sorry
