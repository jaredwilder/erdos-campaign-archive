import Mathlib

set_option autoImplicit false


def phi (m : Nat) : Nat := (List.range (m+1)).filter (fun k => Nat.gcd k m == 1) |>.length

def isPrime (n : Nat) : Bool :=
  n >= 2 && (List.range (n-1)).drop 2 |>.all (fun d => d == 0 || n % d != 0)

def leastPrimeOneMod (n : Nat) : Option Nat :=
  (List.range 10000).map (fun k => n * k + 1) |>.find isPrime

def mOf (n : Nat) : Option Nat :=
  (List.range 10000).map (fun k => k + 1) |>.find (fun m => n % phi m == 0 || phi m % n == 0 && n ≤ phi m)

def eqSetCheck : Bool :=
  (List.range 20).drop 1 |>.all (fun i =>
    let n := i + 1
    match mOf n, leastPrimeOneMod n with
    | some m, some p => (m == p) == ((n ∈ [2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19]))
    | _, _ => false)

def strictWitnessCheck : Bool :=
  phi 15 % 8 == 0 && 15 < 8 * 1 + 1 -- placeholder replaced below

def strictWitnesses : Bool :=
  match mOf 8, leastPrimeOneMod 8, mOf 20, leastPrimeOneMod 20 with
  | some m8, some p8, some m20, some p20 =>
      p8 == 17 && m8 == 15 && m8 < p8 && p20 == 41 && m20 == 25 && m20 < p20
  | _, _, _, _ => false

def leCheck : Bool :=
  (List.range 20).drop 1 |>.all (fun i =>
    let n := i + 1
    match mOf n, leastPrimeOneMod n with
    | some m, some p => m ≤ p
    | _, _ => false)

def checkL1 : Bool := leCheck && eqSetCheck && strictWitnesses

theorem msl_fmz_erdos456_campaign_001_R009_L1_a1r1  : checkL1 = true := by decide

-- axiom footprint
#print axioms phi
#print axioms isPrime
#print axioms leastPrimeOneMod
#print axioms mOf
#print axioms eqSetCheck
#print axioms strictWitnessCheck
#print axioms strictWitnesses
#print axioms leCheck
#print axioms checkL1
#print axioms msl_fmz_erdos456_campaign_001_R009_L1_a1r1
