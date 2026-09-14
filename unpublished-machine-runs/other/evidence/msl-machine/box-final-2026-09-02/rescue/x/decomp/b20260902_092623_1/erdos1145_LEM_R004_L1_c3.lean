import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter Classical

def isConv (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1),
    if (∃ k : ℕ, a k = i) ∧ (∃ k : ℕ, b k = n - i) then 1 else 0

def Erdos1145Prop : Prop :=
∀ (a b : ℕ → ℕ),
  (∀ k : ℕ, 1 ≤ a k ∧ a k < a (k + 1)) →
  (∀ k : ℕ, 1 ≤ b k ∧ b k < b (k + 1)) →
  Filter.Tendsto (fun k => ((a k : ℚ) / (b k : ℚ))) Filter.atTop (nhds (1 : ℚ)) →
  (∃ N : ℕ, ∀ n ≥ N, ∃ i j : ℕ, a i + b j = n) →
  Filter.limsup (fun n => ((isConv a b n : ℕ) : ENNReal)) Filter.atTop = ⊤

theorem msl_erdos1145_lem_r004_l1_c3 (a b : ℕ → ℕ) (N : ℕ) : (∀ k : ℕ, 1 ≤ a k ∧ a k < a (k + 1)) → (∀ k : ℕ, 1 ≤ b k ∧ b k < b (k + 1)) →
 (∀ n ≥ N, ∃ i j : ℕ, a i + b j = n) →
 ∃ n ≥ N, isConv a b n ≥ 1 := by sorry
