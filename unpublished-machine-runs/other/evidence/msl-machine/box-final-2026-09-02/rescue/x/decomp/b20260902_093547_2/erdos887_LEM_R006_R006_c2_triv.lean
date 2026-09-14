import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
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

theorem msl_erdos887_lem_r006_r006_c2_triv (n : Nat) (C C' : ℝ) : C ≤ C' → (divisorsInWindow n C).card ≤ (divisorsInWindow n C').card := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
