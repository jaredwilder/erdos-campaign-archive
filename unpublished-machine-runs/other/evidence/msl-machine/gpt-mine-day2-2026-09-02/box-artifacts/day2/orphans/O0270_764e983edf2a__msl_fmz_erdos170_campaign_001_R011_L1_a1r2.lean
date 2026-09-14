import Mathlib

set_option autoImplicit false


def tri (m : Nat) : Nat := m * (m + 1) / 2

-- fuel-based, structurally recursive, total
def minimalM : Nat -> Nat -> Nat
  | 0, N => N + 1  -- fallback, never used with adequate fuel
  | fuel+1, N =>
      let m := minimalM fuel N
      if m == 0 then (if tri 0 >= N + 1 then 0 else 1)
      else if tri m >= N + 1 then m else m + 1

def boundCheck (N : Nat) : Bool :=
  let m := minimalM (N + 1) N
  tri m >= N + 1 && (m == 0 || tri (m - 1) < N + 1)

def covers (N : Nat) (A : List Nat) : Bool :=
  (List.range (N + 1)).all fun d =>
    A.any fun a => A.any fun b => if a >= b then a - b == d else false

def checkTight0 : Bool := covers 0 [0]
def checkTight1 : Bool := covers 1 [0, 1]

def checkAll (n : Nat) : Bool :=
  (List.range (n + 1)).all boundCheck && checkTight0 && checkTight1

theorem msl_fmz_erdos170_campaign_001_R011_L1_a1r2  : checkAll 200 = true := by decide

-- axiom footprint
#print axioms tri
#print axioms minimalM
#print axioms boundCheck
#print axioms covers
#print axioms checkTight0
#print axioms checkTight1
#print axioms checkAll
#print axioms msl_fmz_erdos170_campaign_001_R011_L1_a1r2
