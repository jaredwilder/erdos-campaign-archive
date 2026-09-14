import Mathlib

set_option autoImplicit false



open Nat in

def bound : Nat := 199

def candPairs : List (Nat × Nat) :=
  (List.range 8).flatMap (fun a => (List.range 6).map (fun b => (a, b)))

def val (ab : Nat × Nat) : Nat := 2^(ab.1) * 3^(ab.2)

def class1Cand : List Nat :=
  (candPairs.map val).filter (fun n => n - 1 ≤ bound && 1 < n - 1 && Nat.Prime (n - 1))

def enumerated : List Nat := (class1Cand.map (· - 1)).eraseDups

def expected : List Nat :=
  [2, 3, 5, 7, 11, 17, 23, 31, 47, 53, 71, 107, 127, 191]

def eachExpectedIsClass1 : Prop :=
  ∀ p ∈ expected, ∃ a : Nat, ∃ b : Nat, 2^a * 3^b = p + 1 ∧ Nat.Prime p

def decEachExpected : Bool :=
  expected.all (fun p => decide (∃ a : Nat, ∃ b : Nat, 2^a * 3^b = p + 1 ∧ Nat.Prime p))

def noExtra : Bool :=
  expected.all (fun p => enumerated.count p == 1) && (enumerated.all (· ∈ expected))

def check_enumeration : Bool :=
  decEachExpected && noExtra && (expected.length == 14) &&
  (enumerated.all (fun p => p ≤ 199))

theorem msl_fmz_erdos1055_campaign_001_R005_L1  : check_enumeration = true ∧ eachExpectedIsClass1 := by decide

-- axiom footprint
#print axioms bound
#print axioms candPairs
#print axioms val
#print axioms class1Cand
#print axioms enumerated
#print axioms expected
#print axioms eachExpectedIsClass1
#print axioms decEachExpected
#print axioms noExtra
#print axioms check_enumeration
#print axioms msl_fmz_erdos1055_campaign_001_R005_L1
