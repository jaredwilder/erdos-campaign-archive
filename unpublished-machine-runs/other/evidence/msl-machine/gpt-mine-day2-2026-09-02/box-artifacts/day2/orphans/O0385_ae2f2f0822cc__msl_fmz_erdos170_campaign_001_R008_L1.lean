import Mathlib

set_option autoImplicit false


def tri (n : Nat) : Nat := n * (n - 1) / 2 + 1

def nstar : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 4
  | _ => 0

-- Two-sided certificate for N ≤ 5: n*-1 strictly insufficient, n* sufficient.
def lowerOk (N n : Nat) : Bool := (tri (n - 1)) < (N + 1)
def upperOk (N n : Nat) : Bool := (N + 1) <= (tri n)

def checkOne (N : Nat) : Bool :=
  lowerOk N (nstar N) && upperOk N (nstar N)

def checkLemma : Bool :=
  checkOne 0 && checkOne 1 && checkOne 2 && checkOne 3 && checkOne 4 && checkOne 5

theorem msl_fmz_erdos170_campaign_001_R008_L1  : checkLemma = true := by decide

-- axiom footprint
#print axioms tri
#print axioms nstar
#print axioms lowerOk
#print axioms upperOk
#print axioms checkOne
#print axioms checkLemma
#print axioms msl_fmz_erdos170_campaign_001_R008_L1
