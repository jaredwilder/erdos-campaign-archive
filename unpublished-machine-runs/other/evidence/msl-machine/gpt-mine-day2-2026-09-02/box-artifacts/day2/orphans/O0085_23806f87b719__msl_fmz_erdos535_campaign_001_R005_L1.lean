import Mathlib

set_option autoImplicit false


def gcdN : Nat → Nat → Nat
  | a, 0 => a
  | a, b+1 => gcdN b (a % (b+1))

/-- A chain is a list of naturals; check divisibility pairwise-adjacent. -/
def divChain : List Nat → Bool
  | [] => true
  | [_] => true
  | x1 :: x2 :: rest => x2 % x1 == 0 && divChain (x2 :: rest)

/-- L1 core: for a divisibility chain of length ≥ 2, gcd of first and last equals the first, and the last is divisible by the first. -/
def l1Check (xs : List Nat) : Bool :=
  match xs with
  | [] => true
  | [_] => true
  | x1 :: rest =>
    match rest.getLast? with
    | none => true
    | some xr => gcdN x1 xr == x1 && xr % x1 == 0

/-- All increasing sequences of length k with values in [1,64]. -/
def allSeqs (k : Nat) : List (List Nat) :=
  match k with
  | 0 => [[]]
  | (k+1) => (List.range 64).flatMap (fun i =>
      (allSeqs k).map (fun l => (i+1) :: l))

def checkAll : Bool :=
  (List.range 8).all (fun k =>
    (allSeqs (k+1)).all (fun xs => divChain xs == true → l1Check xs == true))

theorem msl_fmz_erdos535_campaign_001_R005_L1  : checkAll = true := by native_decide

-- axiom footprint
#print axioms gcdN
#print axioms divChain
#print axioms l1Check
#print axioms allSeqs
#print axioms checkAll
#print axioms msl_fmz_erdos535_campaign_001_R005_L1
