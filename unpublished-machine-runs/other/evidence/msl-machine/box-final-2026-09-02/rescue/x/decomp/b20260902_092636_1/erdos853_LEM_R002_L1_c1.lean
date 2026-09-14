import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def primeAt (n : Nat) : Nat := Nat.nth Nat.Prime n

def d (n : Nat) : Nat := primeAt (n + 1) - primeAt n

/-- Infinitely many consecutive-prime gaps equal to 2 (the t = 2 instance). -/
def TwinGap : Prop := ∀ (N : Nat), ∃ (n : Nat), N ≤ n ∧ d n = 2

/-- The twin prime conjecture: infinitely many primes k with k + 2 prime. -/
def TwinPair : Prop := ∀ (N : Nat), ∃ (k : Nat), N ≤ k ∧ Nat.Prime k ∧ Nat.Prime (k + 2)

theorem msl_erdos853_lem_r002_l1_c1 : TwinGap → TwinPair := by sorry
