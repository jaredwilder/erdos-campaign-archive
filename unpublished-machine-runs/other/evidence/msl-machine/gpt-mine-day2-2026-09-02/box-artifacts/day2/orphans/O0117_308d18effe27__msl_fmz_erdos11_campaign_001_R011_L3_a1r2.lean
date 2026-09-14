import Mathlib

set_option autoImplicit false


-- Squarefree test by trial division of the smallest prime factor, exact Nat arithmetic.
def squarefreeAux (d : Nat) (n : Nat) : Bool :=
  if d * d > n then true
  else if n % d == 0 then false
  else squarefreeAux (d+1) n

def Squarefree' (n : Nat) : Bool :=
  match n with
  | 0 => false
  | 1 => true
  | n+2 => squarefreeAux 2 (n+2)

def pow2 (l : Nat) : Nat := 2 ^ l

-- Each entry: (n, l, k) with claim: n odd, n>1, n = k + 2^l, Squarefree' k = true.
def witnesses : List (Nat × Nat × Nat) :=
  [(3,1,1),(5,2,1),(7,1,5),(9,3,1),(11,1,9),(13,2,9),(15,1,13),(17,4,1),
   (19,1,17),(21,2,17),(23,1,21),(25,3,17),(27,1,25),(29,2,25),(31,1,29),
   (33,4,17),(35,1,33),(37,2,33),(39,1,37),(41,3,33),(43,1,41),(45,2,41),
   (47,1,45),(49,4,33),(51,1,49),(53,2,49),(55,1,53),(57,3,49),(59,1,57),
   (61,2,57),(63,1,61)]

def checkEntry : Nat × Nat × Nat -> Bool
  | (n, l, k) =>
      n % 2 == 1 && n > 1 && Squarefree' k && n == k + pow2 l

def checkAll : Bool := witnesses.all checkEntry

def count31 : Bool := witnesses.length == 31

theorem msl_fmz_erdos11_campaign_001_R011_L3_a1r2  : checkAll = true ∧ count31 = true := by decide

-- axiom footprint
#print axioms squarefreeAux
#print axioms Squarefree'
#print axioms pow2
#print axioms witnesses
#print axioms checkEntry
#print axioms checkAll
#print axioms count31
#print axioms msl_fmz_erdos11_campaign_001_R011_L3_a1r2
