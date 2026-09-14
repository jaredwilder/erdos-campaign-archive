import Mathlib

set_option autoImplicit false


def gcdUniform (s : List Nat) : Bool :=
  match s with
  | [] => true
  | a :: t =>
    (t.all (fun b => Nat.gcd a b == Nat.gcd a b))
    && match t with
       | [] => true
       | b :: t2 =>
         (t2.all (fun c => Nat.gcd a b != Nat.gcd a c && Nat.gcd b c != Nat.gcd a c))
         && gcdUniform t

def subsets : Nat -> List (List Nat)
  | 0 => [[]]
  | n + 1 =>
    let rest := subsets n
    rest ++ rest.map (fun s => (n + 1) :: s)

def f3 (m : Nat) : Nat :=
  (subsets m).foldl (fun acc s =>
    if s.length >= 3 && gcdUniform s then max acc s.length else acc) 0

def checkL1 : Bool :=
  f3 3 == 2 && f3 4 == 3 && f3 5 == 3

theorem msl_fmz_erdos535_campaign_001_R003_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms gcdUniform
#print axioms subsets
#print axioms f3
#print axioms checkL1
#print axioms msl_fmz_erdos535_campaign_001_R003_L1
