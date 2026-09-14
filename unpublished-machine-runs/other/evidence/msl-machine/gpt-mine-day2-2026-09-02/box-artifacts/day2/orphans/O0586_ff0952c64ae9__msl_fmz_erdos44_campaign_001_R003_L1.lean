import Mathlib

set_option autoImplicit false


def validSig (s : List Int) : Bool :=
  match s with
  | [a, b, c, m] => c == a * b * m && m > 0
  | _ => false

def certAccept (sig : List Int) (claim : Int) : Bool :=
  if validSig sig then claim > 0 else false

def checkFailClosed : Bool :=
  certAccept [] 1 == false
  && certAccept [1, 2, 3] 1 == false
  && certAccept [1, 2, 3, 0] 1 == false
  && certAccept [1, 2, 3, (-2)] 1 == false
  && certAccept [1, 2, 5, 4] 1 == false

def checkAccepts : Bool :=
  certAccept [2, 3, 12, 2] 1 == true

def checkDeterministic : Bool :=
  certAccept [2, 3, 12, 2] 1 == certAccept [2, 3, 12, 2] 1
  && certAccept [3, 3, 9, 1] 0 == false
  && certAccept [3, 3, 9, 1] 0 == certAccept [3, 3, 9, 1] 0

def checkL1Fragment : Bool :=
  checkFailClosed && checkAccepts && checkDeterministic

theorem msl_fmz_erdos44_campaign_001_R003_L1  : checkL1Fragment = true := by decide

-- axiom footprint
#print axioms validSig
#print axioms certAccept
#print axioms checkFailClosed
#print axioms checkAccepts
#print axioms checkDeterministic
#print axioms checkL1Fragment
#print axioms msl_fmz_erdos44_campaign_001_R003_L1
