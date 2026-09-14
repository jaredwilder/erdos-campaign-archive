import Mathlib

set_option autoImplicit false


def chordClasses (n : Nat) : Nat :=
  (List.range (n - 1) |>.map (fun k => min (k + 1) (n - (k + 1)))) |>.eraseDups.length

def checkRange : List Nat := (List.range 62).map (fun i => i + 3)

def cocircularClassCount : Bool :=
  checkRange.all (fun n => chordClasses n == n / 2)

theorem msl_fmz_erdos653_campaign_001_R005_L1  : cocircularClassCount = true := by decide

-- axiom footprint
#print axioms chordClasses
#print axioms checkRange
#print axioms cocircularClassCount
#print axioms msl_fmz_erdos653_campaign_001_R005_L1
