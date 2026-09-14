import Mathlib

set_option autoImplicit false


def pigeonhole (n : Nat) : Bool := 2 ^ ((n - 1).log2) < n
def checkRange (N : Nat) : Bool := (List.range (N - 2)).all (fun i => pigeonhole (i + 2))

theorem msl_fmz_erdos624_campaign_001_R006_L1  : checkRange 64 = true := by decide

-- axiom footprint
#print axioms pigeonhole
#print axioms checkRange
#print axioms msl_fmz_erdos624_campaign_001_R006_L1
