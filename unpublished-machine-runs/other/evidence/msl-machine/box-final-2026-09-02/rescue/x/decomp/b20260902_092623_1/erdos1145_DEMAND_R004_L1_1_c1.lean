import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def SeqStrict (f : ℕ → ℕ) : Prop := ∀ n : ℕ, 1 ≤ f n ∧ f n < f (n + 1)

def sumsetMem (a b : ℕ → ℕ) (m : ℕ) : Prop := ∃ i j : ℕ, a i + b j = m

def convAB (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n).filter
    (fun p : ℕ × ℕ => a p.1 + b p.2 = n)).card

theorem msl_erdos1145_demand_r004_l1_1_c1 (a : ℕ → ℕ) (b : ℕ → ℕ) : ∀ (a b : ℕ → ℕ), SeqStrict a → SeqStrict b → ∀ m : ℕ, 2 ≤ m →
 sumsetMem a b m → ∃ i j : ℕ, i < m ∧ j < m ∧ a i + b j = m := by sorry
