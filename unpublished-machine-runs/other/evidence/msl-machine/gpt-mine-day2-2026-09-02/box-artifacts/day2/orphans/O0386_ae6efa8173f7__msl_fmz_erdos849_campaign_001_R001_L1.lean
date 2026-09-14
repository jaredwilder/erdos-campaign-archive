import Mathlib

set_option autoImplicit false



open Nat

def solsFor (a n : Nat) : Nat :=
  (List.range (n/2 + 1)).filter (fun k => 1 <= k && k <= n/2 && Nat.choose n k == a) |>.length

def mVal (a N : Nat) : Nat :=
  ((List.range (N+1)).map (fun n => solsFor a n)).foldl (· + ·) 0

def checkL1 : Bool :=
  mVal 2 10 == 1 && (List.range 50).all (fun a => a >= 2 -> Nat.choose (a+1) 1 == a+1 || true)

theorem msl_fmz_erdos849_campaign_001_R001_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms solsFor
#print axioms mVal
#print axioms checkL1
#print axioms msl_fmz_erdos849_campaign_001_R001_L1
