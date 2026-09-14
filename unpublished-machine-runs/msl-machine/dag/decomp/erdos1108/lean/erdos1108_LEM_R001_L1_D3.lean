import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def factTable : Finset ℕ :=
  {(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (9 : ℕ), (10 : ℕ), (11 : ℕ), (14 : ℕ), (15 : ℕ)}

def sqRes : Finset ℕ :=
  {(0 : ℕ), (1 : ℕ), (4 : ℕ), (9 : ℕ)}

def sqTable : Finset ℕ :=
  {(0 : ℕ), (1 : ℕ), (9 : ℕ)}

def badTable : Finset ℕ :=
  {(4 : ℕ), (5 : ℕ), (12 : ℕ), (13 : ℕ)}

/-- Elements of A: finite sums of factorials of positive integers (the corrected table {1, 2, 6, 8, 8}
comes from 1!, 2!, 3!, 4!, 5! mod 16, so 0! does not contribute; the hypothesis 1 ≤ n encodes this). -/
def factA : Set ℕ :=
  {a : ℕ | ∃ S : Finset ℕ, (∀ n ∈ S, (1 : ℕ) ≤ n) ∧ a = ∑ n ∈ S, Nat.factorial n}

theorem msl_erdos1108_lem_r001_l1_c3 (S : Finset ℕ) : (∀ n ∈ S, (1 : ℕ) ≤ n) → (∑ n ∈ S, Nat.factorial n) % (16 : ℕ) = (∑ n ∈ S ∩ Finset.Icc (1 : ℕ) (5 : ℕ), Nat.factorial n) % (16 : ℕ) := by sorry
