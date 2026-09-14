import Mathlib

set_option autoImplicit false


def bit (mask i : Nat) : Bool := mask / 2^i % 2 == 1

def triple (a b c : Nat) : Bool :=
  Nat.gcd a b == Nat.gcd a c && Nat.gcd a c == Nat.gcd b c

-- does the subset { i : bit i of mask set, 1 <= i <= n } contain a 3-subset
-- with all pairwise gcds equal? Fuel-indexed scan over i < j < k in [1,n].
def badTripleExists (n mask : Nat) : Bool :=
  go ((n+1)*(n+1)*(n+1)) 1 2 3
where
  go : Nat -> Nat -> Nat -> Nat -> Bool
    | 0, _, _, _ => false
    | f+1, i, j, k =>
      if i > n then false
      else if j > n then go f (i+1) (i+2) (i+3)
      else if k > n then go f i (j+1) (j+2)
      else if bit mask i && bit mask j && bit mask k && triple i j k then true
      else go f i j (k+1)

def valid (n mask : Nat) : Bool := !(badTripleExists n mask)

-- cardinality of the subset encoded by mask (bits 1..n)
def size (n mask : Nat) : Nat := cnt ((n+1)*(n+1)) 1 0
where
  cnt : Nat -> Nat -> Nat -> Nat
    | 0, _, acc => acc
    | f+1, i, acc =>
      if i > n then acc
      else cnt f (i+1) (acc + (if bit mask i then 1 else 0))

-- exhaustive maximum size of a valid subset of [n]
def best (n : Nat) : Nat := go (2^n) 0 0
where
  go : Nat -> Nat -> Nat -> Nat
    | 0, _, acc => acc
    | f+1, m, acc =>
      if valid n m then go f (m+1) (Nat.max acc (size n m))
      else go f (m+1) acc

def check : Bool :=
  best 3 == 2 && best 4 == 3 && best 5 == 3 && best 6 == 3
  -- witness {1,3} for f_3(3) = 2
  && valid 3 5 && size 3 5 == 2
  -- witness {1,2,4} for f_3(4) = 3, embedding in [5] and [6]
  && valid 4 11 && size 4 11 == 3
  && valid 5 11 && valid 6 11

theorem msl_fmz_erdos535_campaign_001_R010_L1  : check = true := by decide

-- axiom footprint
#print axioms bit
#print axioms triple
#print axioms badTripleExists
#print axioms valid
#print axioms size
#print axioms best
#print axioms check
#print axioms msl_fmz_erdos535_campaign_001_R010_L1
