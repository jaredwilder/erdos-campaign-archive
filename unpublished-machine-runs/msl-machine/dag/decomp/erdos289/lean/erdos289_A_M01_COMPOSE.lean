import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset

-- campaign vocabulary, already kernel-checked (msl_decompose)
def runSum (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n

def runProd (a b : ℕ) : ℕ := ∏ n ∈ Icc a b, n

def runNum (a b : ℕ) : ℕ := ∑ n ∈ Icc a b, runProd a b / n

-- proposed definitions

theorem msl_erdos289_a_m01_composition : ((∀ (n : Nat), 2 ≤ n → ((1 : ℚ) / n = (1 : ℚ) / (n + 1) + (1 : ℚ) / (n * (n + 1)))) ∧ (∀ (n : Nat), 2 ≤ n → (n + 1) + 1 < n * (n + 1)) ∧ (∀ᶠ k : ℕ in Filter.atTop, ∃ J : Fin k → ℕ × ℕ, (∀ (i : Fin k), 5 ≤ (J i).1 ∧ (J i).1 < (J i).2) ∧ (∀ (i j : Fin k), i ≠ j → (J i).2 < (J j).1 ∨ (J j).2 < (J i).1) ∧ ∑ i, ∑ n ∈ Icc (J i).1 (J i).2, ((n : ℚ)⁻¹) = (1 : ℚ) / 6)) → (∀ᶠ k : ℕ in Filter.atTop, ∃ I : Fin k → ℕ × ℕ, (∀ (i : Fin k), (I i).1 < (I i).2) ∧ (∀ (i j : Fin k), i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧ ∑ i, ∑ n ∈ Icc (I i).1 (I i).2, ((n : ℚ)⁻¹) = (1 : ℚ)) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos289_a_m01_composition
