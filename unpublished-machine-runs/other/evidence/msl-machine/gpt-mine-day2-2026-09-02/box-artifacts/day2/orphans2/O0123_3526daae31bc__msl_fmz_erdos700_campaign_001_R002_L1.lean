import Mathlib

set_option autoImplicit false

namespace Day2Wrap


def terms (n : Nat) : List Int :=
  (List.range n).map (fun k => ((k + 1 : Nat) - k : Nat))

def telesum (n : Nat) : Int := (terms n).sum

def residual (n : Nat) : Int := telesum n - (n : Int)

def check : Bool :=
  (List.range 20).all (fun n => residual n == 0)

theorem msl_fmz_erdos700_campaign_001_R002_L1  : check = true := by decide

end Day2Wrap
-- axiom footprint
#print axioms Day2Wrap.terms
#print axioms Day2Wrap.telesum
#print axioms Day2Wrap.residual
#print axioms Day2Wrap.check
#print axioms Day2Wrap.msl_fmz_erdos700_campaign_001_R002_L1
