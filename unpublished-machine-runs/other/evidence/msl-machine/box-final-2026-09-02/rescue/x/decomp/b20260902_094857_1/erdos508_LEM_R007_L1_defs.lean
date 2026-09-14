import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def PlaneColoring (k : Nat) (c : EuclideanSpace ℝ (Fin 2) → Fin k) : Prop :=
  ∀ (p q : EuclideanSpace ℝ (Fin 2)), dist p q = (1:ℝ) → c p ≠ c q

def PlaneNoColoring (k : Nat) : Prop :=
  ∀ (c : EuclideanSpace ℝ (Fin 2) → Fin k), ¬ PlaneColoring k c

def UnitDistEdges (V : Finset (EuclideanSpace ℝ (Fin 2))) (E : Finset (V × V)) : Prop :=
  ∀ (e : V × V), e ∈ E → dist e.1 e.2 = (1:ℝ)
