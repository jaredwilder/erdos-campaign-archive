import Mathlib

set_option autoImplicit false


def pairingSum : Nat -> Nat
  | 0 => 0
  | (n+1) => pairingSum n + (n+1)

def closedForm (n : Nat) : Nat := n * (n + 1) / 2

def checkPairing : Nat -> Bool
  | 0 => True
  | (n+1) => (pairingSum (n+1) == closedForm (n+1)) && checkPairing n

def checkSignZero : Nat -> Bool
  | 0 => True
  | (n+1) =>
      let s := pairingSum (n+1)
      let c := closedForm (n+1)
      (s >= c) && (c >= s) && checkSignZero n

theorem msl_fmz_erdos566_campaign_001_R002_L1  : checkPairing 60 = true && checkSignZero 60 = true := by decide

-- axiom footprint
#print axioms pairingSum
#print axioms closedForm
#print axioms checkPairing
#print axioms checkSignZero
#print axioms msl_fmz_erdos566_campaign_001_R002_L1
