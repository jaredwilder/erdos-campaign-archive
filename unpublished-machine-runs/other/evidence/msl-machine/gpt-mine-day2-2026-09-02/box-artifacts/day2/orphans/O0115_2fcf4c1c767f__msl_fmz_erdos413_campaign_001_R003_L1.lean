import Mathlib

set_option autoImplicit false


def isPrime : Nat -> Bool
  | 0 => false | 1 => false
  | n => (List.range (n-1)).drop 1 |>.all (fun d => n % (d+1) != 0)

def omega (n : Nat) : Nat :=
  (List.range (n+1)).filter (fun p => isPrime p) |>.filter (fun p => n % p == 0) |>.length

def ok (n : Nat) : Bool :=
  (List.range n).all (fun m => m + omega m <= n)

def check_witness : Bool :=
  (List.range 7).all (fun n => ok n) && !ok 7

theorem msl_fmz_erdos413_campaign_001_R003_L1  : check_witness = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms omega
#print axioms ok
#print axioms check_witness
#print axioms msl_fmz_erdos413_campaign_001_R003_L1
