import Mathlib

set_option autoImplicit false


-- Exact integer surrogate for the strict box (0, p^{3/4}): x is inside iff x^4 < p^3,
-- written with explicit multiplications to keep the kernel computation small.
def inBox (p x : Nat) : Bool := x * x * x * x < p * p * p

def inv (p a b : Nat) : Bool := a * b % p == 1

-- (i) Witnesses for n = 0: pairs (p, a, b) with ab ≡ 1 (mod p), a and b both in the box.
def w1 : Bool := inv 5 2 3  && inBox 5 2 && inBox 5 3

def w2 : Bool := inv 7 2 4  && inBox 7 2 && inBox 7 4

def w3 : Bool := inv 11 2 6 && inBox 11 2 && inBox 11 6

def w4 : Bool := inv 101 6 17 && inBox 101 6 && inBox 101 17

-- (ii) p = 13, n = 0: for a = 2, 3, 4 (i.e. k = 1, 2, 3) NO b in [0,13) satisfies
-- both ab ≡ 1 (mod 13) and inBox 13 b. Written as explicit conjunctions over the
-- thirteen candidate b values so the kernel evaluates a fixed small Bool tree.
def noInv13 (a : Nat) : Bool :=
  !((inv 13 a 0 && inBox 13 0)  || (inv 13 a 1 && inBox 13 1)  ||
    (inv 13 a 2 && inBox 13 2)  || (inv 13 a 3 && inBox 13 3)  ||
    (inv 13 a 4 && inBox 13 4)  || (inv 13 a 5 && inBox 13 5)  ||
    (inv 13 a 6 && inBox 13 6)  || (inv 13 a 7 && inBox 13 7)  ||
    (inv 13 a 8 && inBox 13 8)  || (inv 13 a 9 && inBox 13 9)  ||
    (inv 13 a 10 && inBox 13 10) || (inv 13 a 11 && inBox 13 11) ||
    (inv 13 a 12 && inBox 13 12))

def check_L1 : Bool :=
  w1 && w2 && w3 && w4 && noInv13 2 && noInv13 3 && noInv13 4

theorem msl_fmz_erdos445_campaign_001_R005_L1  : check_L1 = true := by decide

-- axiom footprint
#print axioms inBox
#print axioms inv
#print axioms w1
#print axioms w2
#print axioms w3
#print axioms w4
#print axioms noInv13
#print axioms check_L1
#print axioms msl_fmz_erdos445_campaign_001_R005_L1
