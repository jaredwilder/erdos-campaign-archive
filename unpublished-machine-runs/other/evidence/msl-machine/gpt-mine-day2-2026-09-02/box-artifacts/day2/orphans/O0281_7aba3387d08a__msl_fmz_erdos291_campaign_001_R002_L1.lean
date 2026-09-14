import Mathlib

set_option autoImplicit false



noncomputable def L (n : Nat) : Nat := (List.range n).foldl (fun acc k => Nat.lcm acc (k+1)) 1

def a (n : Nat) : Nat := (List.range n).foldl (fun acc k => acc + (L n)/(k+1)) 0

def numH (m : Nat) : Nat := (a m) / (Nat.gcd (a m) (L m))

def isPrime' (p : Nat) : Bool := Nat.Prime p

def checkPair (n p : Nat) : Bool :=
  isPrime' p && p <= n &&
    ((Nat.gcd (a n) (L n)) % p == 0) == (numH (n/p) % p == 0)

def checkAll (N : Nat) : Bool :=
  (List.range N).all (fun i =>
    let n := i + 1
    (List.range n).all (fun j => checkPair n (j+1)))

theorem msl_fmz_erdos291_campaign_001_R002_L1  : checkAll 12 = true := by decide

-- axiom footprint
#print axioms L
#print axioms a
#print axioms numH
#print axioms isPrime'
#print axioms checkPair
#print axioms checkAll
#print axioms msl_fmz_erdos291_campaign_001_R002_L1
