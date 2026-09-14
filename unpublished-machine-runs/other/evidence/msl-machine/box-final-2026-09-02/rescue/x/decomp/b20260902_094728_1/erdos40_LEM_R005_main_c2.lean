import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def countA (A : Set Nat) (N : Nat) : Nat :=
  (Finset.Icc 1 N |>.filter (fun k => k ∈ A)).card

def convA (A : Set Nat) (n : Nat) : Nat :=
  (Finset.Icc 1 n |>.filter (fun k => k ∈ A ∧ n - k ∈ A)).card

def DensCond (A : Set Nat) (g : Nat → Real) : Prop :=
  ∃ (c : Real), 0 < c ∧ ∀ (N : Nat), 1 ≤ N →
    ((countA A N : Real) ≥ c * (N : Real) ^ ((1 : Real) / 2) / g N)

def GrowsUnbounded (g : Nat → Real) : Prop :=
  ∀ (B : Real), ∃ (N₀ : Nat), ∀ (N : Nat), N₀ ≤ N → g N ≥ B

theorem msl_erdos40_lem_r005_main_c2 (A : Set Nat) (N : Nat) : 1 ≤ N → ∃ n ∈ Finset.Icc 2 (2 * N), (convA A n : Real) * (2 * (N : Real) - 1) ≥ ((countA A N : Real) ^ 2) := by sorry
