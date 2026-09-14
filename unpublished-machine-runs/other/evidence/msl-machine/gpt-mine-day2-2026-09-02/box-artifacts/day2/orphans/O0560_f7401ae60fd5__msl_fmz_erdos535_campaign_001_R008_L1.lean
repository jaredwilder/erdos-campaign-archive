import Mathlib

set_option autoImplicit false


def distinct (a b c : Nat) : Bool := a != b && a != c && b != c

def badGcd (a b c : Nat) : Bool :=
  Nat.gcd a b == Nat.gcd a c && Nat.gcd a c == Nat.gcd b c

-- A set s is valid iff no three DISTINCT elements share the same pairwise gcd.
-- If s has fewer than 3 elements, no distinct triple exists, so the check passes.
def good (s : List Nat) : Bool :=
  s.all fun a => s.all fun b => s.all fun c =>
    !(distinct a b c && badGcd a b c)

def powerset : List Nat -> List (List Nat)
  | [] => [[]]
  | a :: t =>
      let rest := powerset t
      rest ++ rest.map (fun s => a :: s)

-- f_3(N) = largest size of a good subset of {1,...,N}
def maxGood (N : Nat) : Nat :=
  (powerset (List.range' 1 N)).filter good
    |>.foldl (fun acc s => Nat.max acc s.length) 0

def check : Bool :=
  maxGood 3 == 2 && maxGood 4 == 3 && maxGood 5 == 3

theorem msl_fmz_erdos535_campaign_001_R008_L1  : check = true := by decide

-- axiom footprint
#print axioms distinct
#print axioms badGcd
#print axioms good
#print axioms powerset
#print axioms maxGood
#print axioms check
#print axioms msl_fmz_erdos535_campaign_001_R008_L1
