import Mathlib

set_option autoImplicit false


def pow2 : Nat → Nat
  | 0 => 1
  | l + 1 => 2 * pow2 l

def mpow (b : Nat) : Nat → Nat → Nat
  | 0, m => 1 % m
  | e + 1, m => (mpow b e m * (b % m)) % m

def memNat (p : Nat) (l : List Nat) : Bool
  | [] => false
  -- (helper written below as plain recursion)

theorem msl_fmz_erdos11_campaign_001_R006_T1_a1r1  : master = true := by decide

-- axiom footprint
#print axioms pow2
#print axioms mpow
#print axioms memNat
#print axioms msl_fmz_erdos11_campaign_001_R006_T1_a1r1
