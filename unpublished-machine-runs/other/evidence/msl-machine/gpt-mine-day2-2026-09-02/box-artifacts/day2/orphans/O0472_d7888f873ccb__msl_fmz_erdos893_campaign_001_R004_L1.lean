import Mathlib

set_option autoImplicit false


-- Divisor count of a positive integer by brute enumeration
def tau (m : Nat) : Nat := (List.range (m+1)).filter (fun d => d > 0 && m % d == 0) |>.length

-- multiplicative order of 2 mod d for odd d >= 1: least k >= 1 with 2^k ≡ 1 mod d
def ord2 (d : Nat) : Nat := (List.range' 1 d).find? (fun k => (2^k) % d == 1) |>.getD 0

-- number of odd d in [1, 2^k - 1] with ord_d(2) | k
-- (for odd d, ord_d(2) | k  <=>  d | 2^k - 1, so this equals tau(2^k - 1))
def ordCount (k : Nat) : Nat :=
  (List.range (2^k)).filter
    (fun d => d % 2 == 1 && ((2^(ord2 d)) % d == 1) && (ord2 d % k == 0 || k % (ord2 d) == 0 && ord2 d <= k && k % ord2 d == 0))
  -- refined below
|> fun _ => (List.range (2^k)).filter (fun d => d % 2 == 1 && k % (ord2 d) == 0) |>.length

def checkK (k : Nat) : Bool := tau (2^k - 1) == ordCount k

def checkAll (B : Nat) : Bool := (List.range' 1 B).all checkK

theorem msl_fmz_erdos893_campaign_001_R004_L1  : checkAll 24 = true := by decide

-- axiom footprint
#print axioms tau
#print axioms ord2
#print axioms ordCount
#print axioms checkK
#print axioms checkAll
#print axioms msl_fmz_erdos893_campaign_001_R004_L1
