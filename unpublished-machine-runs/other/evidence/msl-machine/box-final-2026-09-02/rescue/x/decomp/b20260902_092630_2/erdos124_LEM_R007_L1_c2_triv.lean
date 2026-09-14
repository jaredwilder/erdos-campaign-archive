import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def InP (d : ℕ) (k : ℕ) (n : ℕ) : Prop :=
  ∃ (N : ℕ) (s : Finset (Fin N)), (∀ i ∈ s, k ≤ (i : ℕ)) ∧ n = ∑ i ∈ s, d ^ (i : ℕ)

def Coverable (r : ℕ) (d : Fin r → ℕ) (k : ℕ) (n : ℕ) : Prop :=
  ∃ (a : Fin r → ℕ), (∀ i : Fin r, InP (d i) k (a i)) ∧ n = ∑ i : Fin r, a i

def GoodBases (r : ℕ) (d : Fin r → ℕ) : Prop :=
  (∀ i : Fin r, (3 : ℕ) ≤ d i) ∧
  (∀ (i j : Fin r), (i : ℕ) < (j : ℕ) → d i < d j) ∧
  ((1 : ℚ) ≤ ∑ i : Fin r, (((d i : ℚ) - 1)⁻¹))

def GcdOne (r : ℕ) (d : Fin r → ℕ) : Prop :=
  ∀ (p : ℕ), Nat.Prime p → ∃ i : Fin r, ¬ (p ∣ d i)

theorem msl_erdos124_lem_r007_l1_c2_triv (r : ℕ) (d : Fin r → ℕ) : GoodBases r d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Coverable r d 0 n := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
