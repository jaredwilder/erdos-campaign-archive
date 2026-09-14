import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def Erdos456.pVal (n : Nat) : Nat := sInf {p : Nat | p.Prime ∧ p ≡ 1 [MOD n]}
def Erdos456.mVal (n : Nat) : Nat := sInf {m : Nat | 1 ≤ m ∧ n ∣ Nat.totient m}
def Erdos456.DensityOne (A : Set Nat) : Prop :=
  ∀ (e : Rat), 0 < e → ∃ (N : Nat), ∀ (n : Nat), N ≤ n →
    (1 - e : Rat) ≤ ((Finset.filter (fun (k : Nat) => k ∈ A) (Finset.Icc 1 n)).card : Rat) / (n : Rat)
def Erdos456.TendsToInfOn (A : Set Nat) (f : Nat → Rat) : Prop :=
  ∀ (B : Rat), ∃ (N : Nat), ∀ (n : Nat), N ≤ n → n ∈ A → B < f n

theorem msl_erdos456_a_m05_c3 : Erdos456.DensityOne Set.univ := by sorry
