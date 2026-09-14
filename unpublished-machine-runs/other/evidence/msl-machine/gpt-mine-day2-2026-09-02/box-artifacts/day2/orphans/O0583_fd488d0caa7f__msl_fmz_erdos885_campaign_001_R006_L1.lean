import Mathlib

set_option autoImplicit false


def inD (n d : Nat) : Bool :=
  (List.range (n.sqrt + 1)).any fun a =>
    n % a == 0 && (n / a - a) == d

def witnessK1 : Bool :=
  let N1 := Nat.lcm 1 2
  inD N1 1 && inD N1 2 && N1 == 2

theorem msl_fmz_erdos885_campaign_001_R006_L1  : witnessK1 = true := by decide

-- axiom footprint
#print axioms inD
#print axioms witnessK1
#print axioms msl_fmz_erdos885_campaign_001_R006_L1
