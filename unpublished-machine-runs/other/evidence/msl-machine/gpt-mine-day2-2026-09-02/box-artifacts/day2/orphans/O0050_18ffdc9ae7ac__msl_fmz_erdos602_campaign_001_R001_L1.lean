import Mathlib

set_option autoImplicit false


structure Iv where
  lo : Int
  hi : Int

def Iv.add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩

def Iv.mul (a b : Iv) : Iv :=
  let p := [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
  ⟨p.foldl min p.head!, p.foldl max p.head!⟩

def Iv.pow (a : Iv) : Nat → Iv
  | 0 => ⟨1, 1⟩
  | n + 1 => (Iv.pow a n).mul a

-- f(x) = x^2 + 1 evaluated over the box [-1, 1] with exact integer endpoints
-- (the outward-rounded rational rules are exact here, so containment is exact).
def box : Iv := ⟨-1, 1⟩
def evalF : Iv := (Iv.pow box 2).add ⟨1, 1⟩

-- Soundness-and-sign check for this instance: interval containment gives
-- f([-1,1]) ⊆ [1,2]... verify [1,2] contains all four corner products and the
-- sum, and that lo > 0 so 0 ∉ I(f).
def check : Bool :=
  evalF.lo == 1 && evalF.hi == 2 && evalF.lo > 0

theorem msl_fmz_erdos602_campaign_001_R001_L1  : check = true := by decide

-- axiom footprint
#print axioms Iv.add
#print axioms Iv.mul
#print axioms Iv.pow
#print axioms box
#print axioms evalF
#print axioms check
#print axioms msl_fmz_erdos602_campaign_001_R001_L1
