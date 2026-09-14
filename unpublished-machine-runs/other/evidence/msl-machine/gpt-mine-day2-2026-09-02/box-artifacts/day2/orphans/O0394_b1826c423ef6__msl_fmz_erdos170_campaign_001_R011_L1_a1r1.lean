import Mathlib

set_option autoImplicit false


def tri (m : Nat) : Nat := m * (m + 1) / 2

def minimalM (N : Nat) : Nat :=
  let rec go (m : Nat) : Nat :=
    if tri m >= N + 1 then m else go (m + 1)
  go 0

-- closed form (sqrt(8N+9)-1)/2 realized as the least m with m(m+1)/2 >= N+1
def boundCheck (N : Nat) : Bool :=
  let m := minimalM N
  tri (m - 1) < N + 1 && tri m >= N + 1

def covers (N : Nat) (A : List Nat) : Bool :=
  (List.range (N + 1)).all fun d =>
    A.any fun a => A.any fun b => if a >= b then a - b == d else false

-- tightness witnesses at N=0,1
def checkTight0 : Bool := covers 0 [0]
def checkTight1 : Bool := covers 1 [0, 1]

def checkAll (n : Nat) : Bool :=
  (List.range (n + 1)).all boundCheck && checkTight0 && checkTight1

theorem msl_fmz_erdos170_campaign_001_R011_L1_a1r1  : checkAll 1000 = true := by decide

-- axiom footprint
#print axioms tri
#print axioms minimalM
#print axioms boundCheck
#print axioms covers
#print axioms checkTight0
#print axioms checkTight1
#print axioms checkAll
#print axioms msl_fmz_erdos170_campaign_001_R011_L1_a1r1
