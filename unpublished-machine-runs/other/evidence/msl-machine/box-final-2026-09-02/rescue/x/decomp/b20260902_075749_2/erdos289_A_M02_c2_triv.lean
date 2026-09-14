import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset
open Filter

def intervalFamily (k : Nat) : Type := Fin k → ℕ × ℕ

def wellFormed {k : Nat} (I : intervalFamily k) : Prop :=
  ∀ i : Fin k, (I i).1 < (I i).2

def separated {k : Nat} (I : intervalFamily k) : Prop :=
  ∀ i j : Fin k, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1

def pairwiseDistinct {k : Nat} (I : intervalFamily k) : Prop :=
  ∀ i j : Fin k, i ≠ j → I i ≠ I j

def familySum {k : Nat} (I : intervalFamily k) : ℚ :=
  ∑ i : Fin k, ∑ n ∈ Icc (I i).1 (I i).2, ((n : ℕ)⁻¹ : ℚ)

theorem msl_erdos289_a_m02_c2_triv : ∀ᶠ k : ℕ in atTop, ∀ I : intervalFamily k, wellFormed I → separated I → pairwiseDistinct I → familySum I = (1 : ℚ) := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
