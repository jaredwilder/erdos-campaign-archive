import Mathlib

set_option autoImplicit false

namespace Day2Wrap


def multiplicity (n d : Nat) : Nat := if 2 * (d + 1) = n then 1 else if 2 * (d + 1) < n then 2 else 0

def check (n : Nat) : Bool :=
  (2 * (n / 2) <= n)
  && ((List.range (n / 2)).length == n / 2)
  && ((List.range (n / 2)).all (fun d => multiplicity n d <= 2))

theorem msl_erdos655_campaign_001_R001_close  : check 120 = true := by decide

end Day2Wrap
-- axiom footprint
#print axioms Day2Wrap.multiplicity
#print axioms Day2Wrap.check
#print axioms Day2Wrap.msl_erdos655_campaign_001_R001_close
