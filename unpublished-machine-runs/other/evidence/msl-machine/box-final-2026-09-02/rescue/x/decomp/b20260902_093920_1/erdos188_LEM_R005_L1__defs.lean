import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def Pt := EuclideanSpace ℝ (Fin 2)

def RedFree (c : Pt → Bool) : Prop :=
  ∀ p q : Pt, c p = true → c q = true → dist p q ≠ (1 : ℝ)

def HasBlueAP (c : Pt → Bool) (k : Nat) : Prop :=
  ∃ (a v : Pt), ‖v‖ = (1 : ℝ) ∧ ∀ i : Fin k, c (a + ((i : Nat) : ℝ) • v) = false

def InS (k : Nat) : Prop :=
  ∃ c : Pt → Bool, RedFree c ∧ ¬ HasBlueAP c k

def s : Set Nat := {k : Nat | InS k}
