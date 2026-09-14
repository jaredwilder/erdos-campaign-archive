import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset

import Mathlib
open Finset

def admissibleCfg (k : ℕ) (I : Fin k → ℕ × ℕ) : Prop :=
  (∀ i : Fin k, 2 ≤ (I i).1 ∧ (I i).1 < (I i).2) ∧
  (∀ i j : Fin k, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧
  (∑ i : Fin k, ∑ n ∈ Finset.Icc (I i).1 (I i).2, ((n : ℕ) : ℚ)⁻¹) = 1

def admissible (k : ℕ) : Prop := ∃ I : Fin k → ℕ × ℕ, admissibleCfg k I

def denSetOf {k : ℕ} (I : Fin k → ℕ × ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i => Finset.Icc (I i).1 (I i).2)

def maxV (S : Finset ℕ) : ℕ := S.sup (fun n => n.factorization 2)

def maxCount (S : Finset ℕ) : ℕ :=
  (S.filter (fun n => n.factorization 2 = maxV S)).card

def parityObstruction (k : ℕ) : Prop :=
  ∀ I : Fin k → ℕ × ℕ, admissibleCfg k I → Odd (maxCount (denSetOf I))

theorem msl_erdos289_b_m01_c2 (k : ℕ) : parityObstruction k → ¬ admissible k := by sorry
