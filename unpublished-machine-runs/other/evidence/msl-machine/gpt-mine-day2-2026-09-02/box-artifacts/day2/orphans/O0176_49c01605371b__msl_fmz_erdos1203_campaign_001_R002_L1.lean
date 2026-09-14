import Mathlib

set_option autoImplicit false


def R := Int × Nat
def rLe : R → R → Bool := fun x y => x.1 * (y.2 : Int) ≤ y.1 * (x.2 : Int)
def rEq : R → R → Bool := fun x y => rLe x y && rLe y x
def rmul : R → R → R := fun x y => (x.1 * y.1, x.2 * y.2)
def rIn : R → R → R → Bool := fun x lo hi => rLe lo x && rLe x hi
def rmin : R → R → R := fun x y => if rLe x y then x else y
def rmax : R → R → R := fun x y => if rLe x y then y else x
def imul : R → R → R → R → (R × R) :=
  fun alo ahi blo bhi =>
    let p1 := rmul alo blo
    let p2 := rmul alo bhi
    let p3 := rmul ahi blo
    let p4 := rmul ahi bhi
    (rmin (rmin p1 p2) (rmin p3 p4), rmax (rmax p1 p2) (rmax p3 p4))
def checkPair : R → R → R → R → Bool :=
  fun alo ahi blo bhi =>
    let I := imul alo ahi blo bhi
    rIn (rmul alo blo) I.1 I.2 && rIn (rmul alo bhi) I.1 I.2
    && rIn (rmul ahi blo) I.1 I.2 && rIn (rmul ahi bhi) I.1 I.2
    && (rEq I.1 (rmul alo blo) || rEq I.1 (rmul alo bhi) || rEq I.1 (rmul ahi blo) || rEq I.1 (rmul ahi bhi))
    && (rEq I.2 (rmul alo blo) || rEq I.2 (rmul alo bhi) || rEq I.2 (rmul ahi blo) || rEq I.2 (rmul ahi bhi))
def checkBattery : Bool :=
  checkPair (-1,2) (1,3) (-5,1) (2,1)
  && checkPair (2,1) (3,1) (-1,1) (4,1)
  && checkPair (-3,1) (-2,1) (-7,2) (-5,2)
  && checkPair (0,1) (1,1) (0,1) (1,1)

theorem msl_fmz_erdos1203_campaign_001_R002_L1  : checkBattery = true := by decide

-- axiom footprint
#print axioms R
#print axioms rLe
#print axioms rEq
#print axioms rmul
#print axioms rIn
#print axioms rmin
#print axioms rmax
#print axioms imul
#print axioms checkPair
#print axioms checkBattery
#print axioms msl_fmz_erdos1203_campaign_001_R002_L1
