import Mathlib

set_option autoImplicit false


def M1 (n : Nat) : Nat := n + 1

def check_injective (bound : Nat) : Bool :=
  List.all (List.range (bound + 1)) fun n =>
    List.all (List.range (bound + 1)) fun m =>
      if M1 n = M1 m then n = m else True

def check_strict (bound : Nat) : Bool :=
  List.all (List.range bound) fun n => M1 n < M1 (n + 1)

theorem msl_fmz_erdos677_campaign_001_R002_L1  : check_injective 64 = true ∧ check_strict 64 = true := by decide

-- axiom footprint
#print axioms M1
#print axioms check_injective
#print axioms check_strict
#print axioms msl_fmz_erdos677_campaign_001_R002_L1
