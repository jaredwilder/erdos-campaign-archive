import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def CoprimeSeq (u : ℕ → ℕ) : Prop :=
  ∀ i j : ℕ, i ≠ j → Nat.gcd (u i) (u j) = 1

def Avoids (u : ℕ → ℕ) : Set ℕ :=
  {n : ℕ | ∀ i : ℕ, ¬ (u i ∣ n)}

def Aseq (u : ℕ → ℕ) : ℕ → ℕ := Nat.nth (Avoids u)

def Tux (u : ℕ → ℕ) (x : ℕ) : ℕ :=
  Nat.findGreatest (fun t : ℕ => (Finset.range t).prod (fun i : ℕ => u i) ≤ x) x

def GapMax (u : ℕ → ℕ) (x : ℕ) : ℕ :=
  (Finset.range x).sup
    (fun k : ℕ => if Aseq u k < x then Aseq u (k + 1) - Aseq u k else 0)

def RecipProd (u : ℕ → ℕ) : ℝ :=
  ∏' i : ℕ, ((1 : ℝ) - 1 / (u i : ℝ))⁻¹

def SeqHyps (u : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, u n < u (n + 1)) ∧ CoprimeSeq u ∧
    Summable (fun i : ℕ => (1 : ℝ) / (u i : ℝ))

def SubexpGrowth (u : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (u n : ℝ) ≤ Real.exp (ε * (n : ℝ))

def GapBound (u : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ x ≥ N,
    (GapMax u x : ℝ) < (1 + ε) * (Tux u x : ℝ) * RecipProd u

theorem msl_erdos1101_demand_r003_l2_1_c1 : ∃ u : ℕ → ℕ, SeqHyps u ∧ SubexpGrowth u := by sorry
