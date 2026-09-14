import Mathlib

set_option autoImplicit false


-- Fragment of L1 certified here: the exact-integer bijection claim that the
-- pairwise-distance set of the collinear AP configuration x_k = (k,0), k=0..n-1,
-- is exactly {1,...,n-1}, for every n in 2..200 (the verifier-certified range of L1).

def dists (i n : Nat) : List Nat :=
  (List.range n).filterMap (fun j =>
    if j = i then none else some (if j < i then i - j else j - i))

def allDists (n : Nat) : List Nat :=
  ((List.range n).flatMap (fun i => dists i n)).eraseDups

def expected (n : Nat) : List Nat := (List.range (n-1)).map (fun k => k + 1)

def check (n : Nat) : Bool := allDists n == expected n

def checkRange : Bool :=
  ((List.range 199).all (fun k => check (k + 2)))

theorem msl_fmz_erdos653_campaign_001_R012_L1  : checkRange = true := by decide

-- axiom footprint
#print axioms dists
#print axioms allDists
#print axioms expected
#print axioms check
#print axioms checkRange
#print axioms msl_fmz_erdos653_campaign_001_R012_L1
