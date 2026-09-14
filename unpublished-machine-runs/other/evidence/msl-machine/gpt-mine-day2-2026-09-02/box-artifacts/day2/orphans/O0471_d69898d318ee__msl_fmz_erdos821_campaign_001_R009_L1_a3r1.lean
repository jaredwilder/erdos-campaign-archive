import Mathlib

set_option autoImplicit false


def phi (m : Nat) : Nat := (List.range m).filter (fun k => Nat.gcd k m == 1) |>.length

def gTable : List Nat := (List.range 65).map (fun n => (List.range 8193).filter (fun m => phi m == n) |>.length)

def anchor : Bool :=
  (gTable[24]! == 10) && (gTable[36]! == 13) && (gTable[60]! == 20)

def tableOK : Bool :=
  (List.range 65).all (fun n => (gTable[n]! == (List.range 8193).filter (fun m => phi m == n) |>.length))

def checkL1 : Bool := tableOK && anchor

theorem msl_fmz_erdos821_campaign_001_R009_L1_a3r1  : checkL1 = true := by decide

-- axiom footprint
#print axioms phi
#print axioms gTable
#print axioms anchor
#print axioms tableOK
#print axioms checkL1
#print axioms msl_fmz_erdos821_campaign_001_R009_L1_a3r1
