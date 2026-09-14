import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def sigmaN (n : Nat) : Nat := ∑ d ∈ Nat.divisors n, d

def trialSigma (n : Nat) : Nat := ∑ d ∈ Finset.Icc 1 n, if n % d = 0 then d else 0

def isAmicable (a b : Nat) : Prop := sigmaN a = sigmaN b ∧ sigmaN a = a + b

def Acount (x : Nat) : Nat :=
  (Finset.filter (fun p : Nat × Nat => p.1 ≤ p.2 ∧ p.2 ≤ x ∧ isAmicable p.1 p.2)
    (Finset.product (Finset.Icc 1 x) (Finset.Icc 1 x))).card

def witnessPairs : List (Nat × Nat) :=
  [(220, 284), (1184, 1210), (2620, 2924), (5020, 5564), (6232, 6368)]

def verifierAgrees (V : Nat → Nat) : Prop := ∀ x ≤ (10 ^ 7 : Nat), V x = Acount x

theorem msl_erdos830_lem_r005_l1_c2 : ∀ n ≤ (10 ^ 7 : Nat), sigmaN n = trialSigma n := by sorry
