import Mathlib

set_option autoImplicit false


def Rval (i n : Nat) : Nat := max (i-1) (n-i)

def valueSet (n : Nat) : List Nat :=
  ((List.range n).map (fun i => Rval (i+1) n)).eraseDups

def expectedSet (n : Nat) : List Nat :=
  List.range' (n/2) (n - n/2)

def checkConfig (n : Nat) : Bool :=
  (valueSet n).sort (· ≤ ·) == (expectedSet n).sort (· ≤ ·)
  && valueSet n).length == n - n/2

def checkRange : Bool :=
  (List.range' 1 400).all checkConfig

theorem msl_fmz_erdos653_campaign_001_R013_L1_a1r2  : checkRange = true := by native_decide

-- axiom footprint
#print axioms Rval
#print axioms valueSet
#print axioms expectedSet
#print axioms checkConfig
#print axioms checkRange
#print axioms msl_fmz_erdos653_campaign_001_R013_L1_a1r2
