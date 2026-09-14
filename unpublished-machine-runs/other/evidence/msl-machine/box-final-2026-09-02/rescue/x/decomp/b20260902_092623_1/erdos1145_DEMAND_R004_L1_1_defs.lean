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
