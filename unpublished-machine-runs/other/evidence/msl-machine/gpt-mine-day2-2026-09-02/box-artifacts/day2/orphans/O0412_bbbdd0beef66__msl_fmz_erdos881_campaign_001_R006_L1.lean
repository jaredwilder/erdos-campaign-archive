import Mathlib

set_option autoImplicit false


-- B = {2^m : m >= 3}; complement C = ℕ\B (positive naturals that are not such powers).
def bigPow2 (n : Nat) : Bool := n >= 8 && 2 ^ (Nat.log2 n) == n

def inC (n : Nat) : Bool := 1 <= n && !bigPow2 n

-- Decidable check: n is in C or is a sum of two elements of C, searched over a bounded box.
def isSum2Box (n box : Nat) : Bool :=
  inC n || (List.range (box + 1)).any (fun a =>
    inC a && n > a && inC (n - a))

def checkAll (bound box : Nat) : Bool :=
  (List.range bound).all (fun i => isSum2Box (i + 1) box)

theorem msl_fmz_erdos881_campaign_001_R006_L1  : checkAll 200 200 = true := by decide

-- axiom footprint
#print axioms bigPow2
#print axioms inC
#print axioms isSum2Box
#print axioms checkAll
#print axioms msl_fmz_erdos881_campaign_001_R006_L1
