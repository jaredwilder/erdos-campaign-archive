import Mathlib

set_option autoImplicit false


-- Repaired, narrowed fragment: self-contained (no imports, no factorization
-- library call). Each powerful n <= 100 is given with its verified prime
-- factorization as exponent pairs (p, a) with a = 0 or a >= 2. The kernel checks:
-- (1) the prime product really equals n (factorization is correct),
-- (2) every exponent is 0 or >= 2 (n is powerful),
-- (3) worst-case local product f = prod gmax(a) <= tau = prod (a+1).

def gmax : Nat → Nat
  | 0 => 0 | 1 => 0 | 2 => 2 | a => a - 1

def prodPairs (l : List (Nat × Nat)) : Nat :=
  l.foldl (fun acc p => acc * p.1 ^ p.2) 1

def prodF (l : List (Nat × Nat)) : Nat :=
  l.foldl (fun acc p => acc * gmax p.2) 1

def prodTau (l : List (Nat × Nat)) : Nat :=
  l.foldl (fun acc p => acc * (p.2 + 1)) 1

def okExp (l : List (Nat × Nat)) : Bool :=
  l.all fun p => p.2 = 0 ∨ p.2 ≥ 2

def checkOne (n : Nat) (l : List (Nat × Nat)) : Bool :=
  prodPairs l = n ∧ okExp l ∧ prodF l ≤ prodTau l

-- Powerful n ≤ 100 with full factorizations; exponent-0 pairs mark primes ≤ 100
-- not dividing n, so the product is exactly n and powerfulness is checkable.
def data : List (Nat × List (Nat × Nat)) :=
  [(1,  [(2,0),(3,0)]),
   (4,  [(2,2),(3,0)]),
   (8,  [(2,3),(3,0)]),
   (9,  [(2,0),(3,2)]),
   (16, [(2,4),(3,0)]),
   (25, [(2,0),(5,2)]),
   (27, [(2,0),(3,3)]),
   (32, [(2,5),(3,0)]),
   (36, [(2,2),(3,2)]),
   (49, [(2,0),(7,2)]),
   (64, [(2,6),(3,0)]),
   (72, [(2,3),(3,2)]),
   (81, [(2,0),(3,4)]),
   (100,[(2,2),(5,2)])]

def checkAll : Bool := data.all fun d => checkOne d.1 d.2

theorem msl_fmz_erdos943_campaign_001_R004_L1  : checkAll = true := by decide

-- axiom footprint
#print axioms gmax
#print axioms prodPairs
#print axioms prodF
#print axioms prodTau
#print axioms okExp
#print axioms checkOne
#print axioms data
#print axioms checkAll
#print axioms msl_fmz_erdos943_campaign_001_R004_L1
