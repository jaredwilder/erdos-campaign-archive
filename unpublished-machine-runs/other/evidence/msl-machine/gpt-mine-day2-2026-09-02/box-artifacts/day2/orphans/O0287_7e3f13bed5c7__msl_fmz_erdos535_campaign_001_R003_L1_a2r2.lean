import Mathlib

set_option autoImplicit false


def tripleGcdEq (a b c : Nat) : Bool :=
  Nat.gcd a b == Nat.gcd a c && Nat.gcd a c == Nat.gcd b c

-- All subsets of [3] = {1,2,3}, as lists, written out explicitly (8 subsets).
def subsets3 : List (List Nat) :=
  [[], [1], [2], [3], [1,2], [1,3], [2,3], [1,2,3]]

def r3Free (s : List Nat) : Bool :=
  match s with
  | [a, b, c] => !(tripleGcdEq a b c)
  | _ => true

def f3_3 : Nat :=
  (subsets3.filter r3Free).map (fun t => t.length) |>.foldr max 0

def check_f3_3 : Bool := f3_3 == 2

theorem msl_fmz_erdos535_campaign_001_R003_L1_a2r2  : check_f3_3 = true := by decide

-- axiom footprint
#print axioms tripleGcdEq
#print axioms subsets3
#print axioms r3Free
#print axioms f3_3
#print axioms check_f3_3
#print axioms msl_fmz_erdos535_campaign_001_R003_L1_a2r2
