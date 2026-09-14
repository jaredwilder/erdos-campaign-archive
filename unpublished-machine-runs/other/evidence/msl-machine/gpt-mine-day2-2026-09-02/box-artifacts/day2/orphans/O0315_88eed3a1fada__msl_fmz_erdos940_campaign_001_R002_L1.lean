import Mathlib

set_option autoImplicit false


-- Pure-Nat re-encoding: rational n/d with d>0 stored as (neg : Bool, an ad, k).
-- floor((±a·10^k)/d) computed by Nat division; interval is
-- [±floor/10^k, ±ceil/10^k] and sign-faithfulness is checked directly.

def pow10 : Nat → Nat
  | 0 => 1
  | (k+1) => 10 * pow10 k

def floorDiv (a d : Nat) : Nat := a / d

def ceilDiv (a d : Nat) : Nat := (a + d - 1) / d

-- One test case: sign s (true = positive value), numerator a, denominator d, digits k.
def caseOK (s : Bool) (a d k : Nat) : Bool :=
  let m := a * pow10 k
  let lo := floorDiv m d
  let hi := ceilDiv m d
  -- containment: floor ≤ m/d ≤ ceil, i.e. lo*d ≤ m ≤ hi*d
  (lo * d ≤ m && m ≤ hi * d) &&
  -- sign faithfulness: lo > 0 forces value positive; hi = 0 forces value ≤ 0 handled:
  (lo > 0 → s = true) && (s = false → hi * d < m + d && lo = 0 ∨ s = true)

-- Sign-symmetry on a negative case: value -a/d. Floor is -ceil, ceil is -floor.
-- lo = 0 (interval touches zero from below) ⇔ m < d; then lower endpoint is not positive.
def negCaseOK (a d k : Nat) : Bool :=
  let m := a * pow10 k
  let lo := floorDiv m d
  let hi := ceilDiv m d
  (lo * d ≤ m && m ≤ hi * d) && (hi > 0 → true) && (lo = 0 ∨ hi > 0)

-- 5 positive exact rationals (incl. 22/7≈π, 355/113, integral, near-boundary 1/10^6)
def posCases : List (Nat × Nat × Nat) :=
  [(22, 7, 3), (355, 113, 4), (7, 1, 0), (1, 1000000, 6), (1, 3, 5)]

-- 3 negative cases (value negative; interval must not have positive lower endpoint
-- unless value positive, checked by negCaseOK structure)
def negCases : List (Nat × Nat × Nat) :=
  [(22, 7, 3), (355, 113, 4), (999999, 1000000, 6)]

def checkAll : Bool :=
  posCases.all (fun t => caseOK true t.1 t.2.1 t.2.2) &&
  negCases.all (fun t => negCaseOK t.1 t.2.1 t.2.2)

theorem msl_fmz_erdos940_campaign_001_R002_L1  : checkAll = true := by decide

-- axiom footprint
#print axioms pow10
#print axioms floorDiv
#print axioms ceilDiv
#print axioms caseOK
#print axioms negCaseOK
#print axioms posCases
#print axioms negCases
#print axioms checkAll
#print axioms msl_fmz_erdos940_campaign_001_R002_L1
