import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def CoprimeSeq (u : ℕ → ℕ) : Prop :=
  ∀ (i j : ℕ), i ≠ j → Nat.gcd (u i) (u j) = 1

def Tux (u : ℕ → ℕ) (x t : ℕ) : Prop :=
  (∏ i ∈ Finset.range t, u i) ≤ x ∧ x < ∏ i ∈ Finset.range (t + 1), u i

def Excluded (u : ℕ → ℕ) (n : ℕ) : Prop := ∀ (i : ℕ), ¬ (u i ∣ n)

def GapOK (u : ℕ → ℕ) (x : ℕ) (B : ℝ) : Prop :=
  ∀ (n m : ℕ), n < x → Excluded u n → Excluded u m → n < m →
    (∀ (l : ℕ), n < l → l < m → ¬ Excluded u l) → ((m - n : ℝ) < B)

def GoodSeq (u : ℕ → ℕ) : Prop :=
  StrictMono u ∧ CoprimeSeq u ∧ Summable (fun i : ℕ => (1 : ℝ) / (u i : ℝ)) ∧
    ∀ (ε : ℝ), 0 < ε → ∃ (N : ℕ), ∀ (x : ℕ), N ≤ x → ∃ (t : ℕ),
      Tux u x t ∧ GapOK u x ((1 + ε) * (t : ℝ) * (∏' i : ℕ, (1 - (1 : ℝ) / (u i : ℝ)))⁻¹)
