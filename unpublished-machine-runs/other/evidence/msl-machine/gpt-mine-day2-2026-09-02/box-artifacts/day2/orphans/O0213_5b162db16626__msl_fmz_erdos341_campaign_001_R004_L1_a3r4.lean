import Mathlib

set_option autoImplicit false


inductive St : Type where
  | pt : St

open St

def M : St → St := fun _ => pt

def orbitFixed : Bool := M pt == pt

def orbitFixedAt : Nat → Bool
  | 0     => true
  | (k+1) => orbitFixedAt k && (M^[k+1] pt == pt)

def orbitChecked : Bool := orbitFixedAt 19

def gapWord : List St := [pt]

def periodOf : Nat := 1

def certCheck : Bool :=
  orbitFixed && orbitChecked && (gapWord.length == 1) && (periodOf == 1)

theorem msl_fmz_erdos341_campaign_001_R004_L1_a3r4  : certCheck = true := by decide

-- axiom footprint
#print axioms M
#print axioms orbitFixed
#print axioms orbitFixedAt
#print axioms orbitChecked
#print axioms gapWord
#print axioms periodOf
#print axioms certCheck
#print axioms msl_fmz_erdos341_campaign_001_R004_L1_a3r4
