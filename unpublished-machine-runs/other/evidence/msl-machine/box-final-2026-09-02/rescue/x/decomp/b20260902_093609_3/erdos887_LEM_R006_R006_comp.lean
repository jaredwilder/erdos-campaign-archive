import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
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

theorem msl_erdos887_lem_r006_r006_composition : ((∀ (n : Nat) (C : ℝ), ∀ (d : Nat), d ∈ divisorsInWindow n C → n / d ∈ divisorsBelowWindow n C ∧ d * (n / d) = n) ∧ (∀ (n : Nat) (C C' : ℝ), C ≤ C' → (divisorsInWindow n C).card ≤ (divisorsInWindow n C').card) ∧ (∃ (K1 : Nat), ∀ (n : Nat), (divisorsInWindow n 1).card ≤ K1) ∧ (∃ (K0 : Nat), ∀ (n : Nat), n ∈ Finset.Icc 1 20000 → (divisorsInWindow n 1).card ≤ K0)) → (∃ (K : Nat), ∀ (C : ℝ), C > 0 → ∃ (N : Nat), ∀ (n : Nat), n ≥ N → (divisorsInWindow n C).card ≤ K) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos887_lem_r006_r006_composition
