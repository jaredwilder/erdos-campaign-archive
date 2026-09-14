import Mathlib

set_option autoImplicit false


def tripleGcdEq (s : List Nat) : Bool :=
  match s with
  | [a, b, c] => Nat.gcd a b == Nat.gcd a c && Nat.gcd a c == Nat.gcd b c
  | _ => false

def r3Free (s : List Nat) : Bool :=
  !((s.sublists.filter (fun t => t.length == 3)).any tripleGcdEq)

def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (subsets xs) ++ (subsets xs).map (fun t => x :: t)

def f3 (m : Nat) : Nat :=
  (subsets (List.range m).map (· + 1)).filter r3Free
    |>.map (fun t => t.length)
    |>.foldr max 0

def check_f3_small : Bool :=
  f3 3 == 2 && f3 4 == 3 && f3 5 == 3 && f3 6 == 3 && f3 7 == 3 && f3 8 == 4

theorem msl_fmz_erdos535_campaign_001_R003_L1_a2r1  : check_f3_small = true := by decide

-- axiom footprint
#print axioms tripleGcdEq
#print axioms r3Free
#print axioms subsets
#print axioms f3
#print axioms check_f3_small
#print axioms msl_fmz_erdos535_campaign_001_R003_L1_a2r1
