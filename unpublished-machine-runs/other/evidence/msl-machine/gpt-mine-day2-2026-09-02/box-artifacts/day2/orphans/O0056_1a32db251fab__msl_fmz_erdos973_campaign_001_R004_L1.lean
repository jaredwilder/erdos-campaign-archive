import Mathlib

set_option autoImplicit false


def Q := Int × Nat  -- (num, den), den > 0, exact rational

def qFloor (n : Int) (d k : Nat) : Int := n * (k:Int) / ((d:Int) * (k:Int)) * 0 + (n / (d:Int))  -- unused helper removed in final def

def roundDown (n : Int) (d : Nat) : Int := n / (d:Int)
def roundUp (n : Int) (d : Nat) : Int := (n + ((d:Int) - 1)) / (d:Int)

def outwardOK (n : Int) (d : Nat) : Bool :=
  roundDown n d * (d:Int) <= n && n <= roundUp n d * (d:Int)

def ivMul (a b : Q) : Q := (a.1 * b.1, a.2 * b.2)

def zeroExcluded (lo hi : Q) : Bool := lo.1 > 0 || hi.1 < 0

def signOf (lo hi : Q) : Option Bool :=
  if zeroExcluded lo hi then some (lo.1 > 0) else none

def chkOutward : Bool := outwardOK 7 3 && outwardOK (-7) 3

def chkSign : Option Bool :=
  signOf (ivMul (2, 15) (2, 5)) (ivMul (2, 15) (2, 5))

def chkAmbiguous : Option Bool :=
  signOf (-1, 2) (1, 2)

theorem msl_fmz_erdos973_campaign_001_R004_L1  : chkOutward = true ∧ chkSign = some true ∧ chkAmbiguous = none := by decide

-- axiom footprint
#print axioms Q
#print axioms qFloor
#print axioms roundDown
#print axioms roundUp
#print axioms outwardOK
#print axioms ivMul
#print axioms zeroExcluded
#print axioms signOf
#print axioms chkOutward
#print axioms chkSign
#print axioms chkAmbiguous
#print axioms msl_fmz_erdos973_campaign_001_R004_L1
