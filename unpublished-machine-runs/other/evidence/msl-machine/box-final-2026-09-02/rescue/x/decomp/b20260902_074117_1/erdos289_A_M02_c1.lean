import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset
open Filter

def isGood (k : ℕ) (I : Fin k → ℕ × ℕ) : Prop :=
  (∀ i : Fin k, (I i).1 < (I i).2) ∧
  (∀ i j : Fin k, i ≠ j → (I i).2 < (I j).1 ∨ (J_unused : Nat := 0) → False) ∧
  True

def isGood' (k : ℕ) (I : Fin k → ℕ × ℕ) : Prop :=
  (∀ i : Fin k, (I i).1 < (I i).2) ∧
  (∀ i j : Fin k, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1)

def schemeSum (k : ℕ) (I : Fin k → ℕ × ℕ) : ℚ :=
  ∑ i : Fin k, ∑ n ∈ Icc (I i).1 (I i).2, (n⁻¹ : ℚ)

def isGoodTail (m : ℕ) (J : Fin m → ℕ × ℕ) : Prop :=
  (∀ i : Fin m, 5 ≤ (J i).1 ∧ (J i).1 < (J i).2) ∧
  (∀ i j : Fin m, i ≠ j → (J i).2 < (J j).1 ∨ (J j).2 < (J i).1)

def tailSum (m : ℕ) (J : Fin m → ℕ × ℕ) : ℚ :=
  ∑ i : Fin m, ∑ n ∈ Icc (J i).1 (J i).2, (n⁻¹ : ℚ)

theorem msl_erdos289_a_m02_c1 : ∑ n ∈ Icc (2 : ℕ) (3 : ℕ), (n⁻¹ : ℚ) = (5 : ℚ) / 6 := by sorry
