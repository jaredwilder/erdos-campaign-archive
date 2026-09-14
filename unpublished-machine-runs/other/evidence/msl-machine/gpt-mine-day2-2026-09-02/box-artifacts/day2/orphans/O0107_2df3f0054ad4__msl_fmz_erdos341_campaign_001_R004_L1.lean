import Mathlib

set_option autoImplicit false


namespace R004L1

-- State space of the degenerate admissible initial set A = {3}: a one-point type.
inductive Pt where
  | p3 : Pt

open Pt

-- The unique endomap on a 1-point state space: M(3) = 3 (structural, no encodings).
def M : Pt → Pt := fun _ => p3

-- Orbit of 3 under iterates of M, k = 0..3, as an explicit finite list.
def orbit : List Pt := [p3, M p3, M (M p3), M (M (M p3))]

-- The Bool-valued finite check, purely decidable:
--  (i)  M(3) = 3 structurally;
--  (ii) every orbit element equals 3 (period-1 orbit, exact equality);
--  (iii) the orbit is closed under M (M of the last element is in the orbit).
def checkL1 : Bool :=
  (M p3 == p3)
  && orbit.all (fun x => x == p3)
  && (orbit.contains (M (orbit.getLastD p3)))

end R004L1

theorem msl_fmz_erdos341_campaign_001_R004_L1  : R004L1.checkL1 = true := by decide

-- axiom footprint
#print axioms R004L1.M
#print axioms R004L1.orbit
#print axioms R004L1.checkL1
#print axioms msl_fmz_erdos341_campaign_001_R004_L1
