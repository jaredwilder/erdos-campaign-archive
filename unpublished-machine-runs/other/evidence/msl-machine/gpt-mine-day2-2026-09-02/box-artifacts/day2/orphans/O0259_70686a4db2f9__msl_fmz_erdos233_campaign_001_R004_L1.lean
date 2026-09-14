import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool :=
  if n < 2 then false else (List.range (n - 1)).all (fun k => k < 2 || n % k != 0)

def primesBelow (m : Nat) : List Nat := (List.range m).filter isPrime

def p (n : Nat) : Nat := (primesBelow 120).getD n 0

def gaps (N : Nat) : List Nat :=
  (List.range (N - 1)).map (fun n => p (n+1) - p n)

def check (N : Nat) : Bool :=
  let g := gaps N
  let lhs := g.foldr (fun d acc => d * d + acc) 0
  let maxd := g.foldr max 0
  let rhs := (List.range (maxd + 1)).foldr (fun h acc =>
    acc + (2*h - 1) * g.count h) 0
  lhs == rhs

theorem msl_fmz_erdos233_campaign_001_R004_L1  : check 10 = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms primesBelow
#print axioms p
#print axioms gaps
#print axioms check
#print axioms msl_fmz_erdos233_campaign_001_R004_L1
