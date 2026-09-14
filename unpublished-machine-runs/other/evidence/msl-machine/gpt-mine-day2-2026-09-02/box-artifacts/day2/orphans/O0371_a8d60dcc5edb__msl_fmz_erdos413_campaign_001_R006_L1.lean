import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool :=
  if n < 2 then false else (List.range (n-1) |>.drop 2).all (fun d => n % d != 0)

def omega (n : Nat) : Nat :=
  (List.range (n+1)).filter (fun p => isPrime p && n % p == 0) |>.length

-- n ∈ B_1 (ε=1 barrier property): ∀ m < n, m + ω(m) ≤ n
def inB1 (n : Nat) : Bool :=
  (List.range n).all (fun m => m + omega m <= n)

-- Lemma side after the change of variable k = n − m (so 1 ≤ k ≤ n−1 when n ≥ 2):
-- ω(n−k) ≤ k/ε with ε = 1, i.e. ω(n−k) ≤ k
def lemmaSide (n : Nat) : Bool :=
  (List.range (n-1)).all (fun k => omega (n - (k+1)) <= k+1)

-- Definitional equivalence of the two predicates, finite scope [2,20]
def checkL1 : Bool :=
  (List.range 19).all (fun i => let n := i + 2; inB1 n == lemmaSide n)

theorem msl_fmz_erdos413_campaign_001_R006_L1  : checkL1 = true := by native_decide

-- axiom footprint
#print axioms isPrime
#print axioms omega
#print axioms inB1
#print axioms lemmaSide
#print axioms checkL1
#print axioms msl_fmz_erdos413_campaign_001_R006_L1
