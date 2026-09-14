import Mathlib

set_option autoImplicit false


def iters : List Nat := [0, 13, 26, 29, 45, 61]
def strictlyIncreasing (l : List Nat) : Bool :=
  match l with
  | [] | [_] => true
  | a :: b :: rest => a < b && strictlyIncreasing (b :: rest)
def check_L1_fragment : Bool :=
  strictlyIncreasing (13 :: 26 :: 29 :: 45 :: 61 :: [])
  && iters.length = 6

theorem msl_fmz_erdos680_campaign_001_R002_L1  : check_L1_fragment = true := by decide

-- axiom footprint
#print axioms iters
#print axioms strictlyIncreasing
#print axioms check_L1_fragment
#print axioms msl_fmz_erdos680_campaign_001_R002_L1
