import Mathlib

set_option autoImplicit false




-- Certifies the checkable fragment of L1: the exact geometric identity
-- 1/(n!-1) = sum_{j>=1} (n!)^{-j}  and  tail = 1/((n!-1)(n!)^J),
-- verified in exact Rational arithmetic with fail-closed equality tests,
-- at concrete finite values of n and J.

def fact : Nat -> Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

-- partial geometric sum sum_{j=1}^{J} m^{-j}, exact rationals
def geomSum (m J : Nat) : Rat :=
  (List.range J).foldl (fun acc j => acc + (1 : Rat) / ((m^(j+1) : Nat) : Rat)) 0

-- exact tail after J terms of the geometric series with ratio 1/m, m>=2:
-- tail = m^{-(J+1)} / (1 - 1/m) = 1 / ((m-1) * m^J)
def exactTail (m J : Nat) : Rat :=
  (1 : Rat) / (((m - 1) * m^J : Nat) : Rat)

def fullValue (m : Nat) : Rat := (1 : Rat) / (((m - 1 : Nat) : Rat))

-- fail-closed identity check: partial sum + exact tail equals 1/(m-1) EXACTLY
def checkIdentity (n J : Nat) : Bool :=
  let m := fact n
  fullValue m == geomSum m J + exactTail m J

-- fail-closed tail bound: tail <= 2 * m^{-(J+1)}  (exact rational inequality)
def checkTailBound (n J : Nat) : Bool :=
  let m := fact n
  exactTail m J <= (2 : Rat) / ((m^(J+1) : Nat) : Rat)

def checkL1 : Bool :=
  ([2, 3, 4, 5] : List Nat).all fun n =>
    checkIdentity n 6 && checkTailBound n 6

theorem msl_fmz_erdos68_campaign_001_R003_L1  : checkL1 = true := by native_decide

-- axiom footprint
#print axioms fact
#print axioms geomSum
#print axioms exactTail
#print axioms fullValue
#print axioms checkIdentity
#print axioms checkTailBound
#print axioms checkL1
#print axioms msl_fmz_erdos68_campaign_001_R003_L1
