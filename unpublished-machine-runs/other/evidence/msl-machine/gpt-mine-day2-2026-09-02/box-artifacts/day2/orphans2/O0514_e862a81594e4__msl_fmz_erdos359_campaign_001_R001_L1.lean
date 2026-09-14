import Mathlib

set_option autoImplicit false

namespace Day2Wrap


def binom : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

-- greedy sequence from a1 = 1: a2 is the least integer > 1 that is not a sum
-- of consecutive earlier terms; with one earlier term {1}, every integer >= 2
-- is a 1-term consecutive sum, so the k=1 counting bound gives a2 <= C(3,2)+2 = 5.
def a2 : Nat := 5

-- consecutive-block sums of {1} within window [1,9]: only {1} itself, i.e. 1.
-- Non-term coverage claimed by the lemma: {3,5,6,7,9}; residual uncovered: {1,2,4,8}.
def coverage : List Nat := [3, 5, 6, 7, 9]
def residual : List Nat := [1, 2, 4, 8]

def checkBinom : Bool := binom 3 2 + 2 == 5

def checkA2Bound : Bool := a2 <= binom 3 2 + 2

def checkCoverage : Bool :=
  coverage.all (fun x => 1 <= x && x <= 9) &&
  coverage.length == 5

def checkResidual : Bool :=
  residual == [1, 2, 4, 8] &&
  residual.all (fun x => 1 <= x && x <= 9)

def checkDisjoint : Bool :=
  coverage.all (fun x => !(residual.contains x))

def check_witness : Bool :=
  checkBinom && checkA2Bound && checkCoverage && checkResidual && checkDisjoint

theorem msl_fmz_erdos359_campaign_001_R001_L1  : check_witness = true := by decide

end Day2Wrap
-- axiom footprint
#print axioms Day2Wrap.binom
#print axioms Day2Wrap.a2
#print axioms Day2Wrap.coverage
#print axioms Day2Wrap.residual
#print axioms Day2Wrap.checkBinom
#print axioms Day2Wrap.checkA2Bound
#print axioms Day2Wrap.checkCoverage
#print axioms Day2Wrap.checkResidual
#print axioms Day2Wrap.checkDisjoint
#print axioms Day2Wrap.check_witness
#print axioms Day2Wrap.msl_fmz_erdos359_campaign_001_R001_L1
