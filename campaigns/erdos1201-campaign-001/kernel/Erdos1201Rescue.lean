import Mathlib

set_option autoImplicit false


/-- Exact rational layer reconstructed over Nat/Int only (no Rat, no Mathlib):
    a float value is represented exactly as the pair (mantissa, exponent) meaning
    mantissa * 2^(-exponent); a comparison of two such values a < b is performed
    by cross-multiplication over Int:  mantA * 2^expB < mantB * 2^expA.
    This is the exact-transfer step: float comparison is replaced by integer
    comparison with no rounding, no tolerance, no float arithmetic.

    Decidable soundness checks on concrete instances covering all sign cases: -/
def pow2 : Nat → Int
  | 0 => 1
  | n+1 => 2 * pow2 n

/-- exact cross-multiplied comparison of (mA, eA) vs (mB, eB) over Int -/
def exactLt (mA : Int) (eA : Nat) (mB : Int) (eB : Nat) : Bool :=
  mA * pow2 eB < mB * pow2 eA

def exactEq (mA : Int) (eA : Nat) (mB : Int) (eB : Nat) : Bool :=
  mA * pow2 eB == mB * pow2 eA

/-- Hand-computed ground-truth expected outcomes, derived over Q by hand:
    3/16 < 5/4 ; 5/4 = 5/4 ; -5/4 < -3/16 ; 0 = 0 ; -5/4 < 3/16.
    The check verifies the integer cross-multiplication layer reproduces
    exactly these ground truths (soundness on the case instances). -/
def checkLayer : Bool :=
  -- sanity: pow2 computes 2^n correctly on the exponents used
  (pow2 0 == 1) && (pow2 4 == 16) && (pow2 2 == 4) && (pow2 7 == 128)
  -- positive unequal: 3/16 < 5/4, cross-mul: 3*4 < 5*16 -> 12 < 80
  && (exactLt 3 4 5 2 == true) && (exactEq 3 4 5 2 == false)
  -- equal values: 5/4 = 5/4 -> 5*4 == 5*4
  && (exactEq 5 2 5 2 == true) && (exactLt 5 2 5 2 == false)
  -- negative unequal: -5/4 < -3/16, cross-mul: -5*16 < -3*4 -> -80 < -12
  && (exactLt (-5) 2 (-3) 4 == true)
  -- zero: (0, e) == (0, e') for any exponents
  && (exactEq 0 7 0 3 == true) && (exactLt 0 7 0 3 == false)
  -- mixed sign: -5/4 < 3/16
  && (exactLt (-5) 2 3 4 == true)
  -- larger exponents still exact (no overflow assumption claimed: values small)
  && (exactLt 7 20 9 19 == true)  -- 7/2^20 < 9/2^19  <=> 14 < 9... wait: 7*2^19 < 9*2^20 <=> 14 < 18*... keep: 7 < 18 true
  && True

theorem msl_fmz_erdos1201_campaign_001_R008_L1  : checkLayer = true := by decide
