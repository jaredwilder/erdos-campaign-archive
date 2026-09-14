import Mathlib

set_option autoImplicit false


def gcd : Nat -> Nat -> Nat
  | 0, m => m
  | (Nat.succ k), m => gcd (m % (k+1)) (k+1)

-- pairwise condition: all pairwise gcds of the chosen set are distinct
-- (any two distinct pairs having equal gcd is forbidden)
def pairwiseGcdsDistinct (s : List Nat) : Bool :=
  let ps := (List.range s.length).flatMap
    (fun i => (List.range s.length).filterMap
      (fun j => if i < j then some (gcd (s.getD i 0) (s.getD j 0)) else none))
  ps.eraseDups.length == ps.length

def subsets : List Nat -> List (List Nat)
  | [] => [[]]
  | x :: xs => let rest := subsets xs
               rest ++ rest.map (fun t => x :: t)

-- f_3(n) = max size of a subset of [n] with distinct pairwise gcds
def fval (n : Nat) : Nat :=
  (subsets (List.range 1 (n+1))).filter pairwiseGcdsDistinct
    |>.foldl (fun acc s => max acc s.length) 0

def checkL1 : Bool :=
  fval 3 == 2 && fval 4 == 3 && fval 5 == 3 && fval 6 == 3

theorem msl_fmz_erdos535_campaign_001_R010_L1_a1r1  : checkL1 = true := by decide

-- axiom footprint
#print axioms gcd
#print axioms pairwiseGcdsDistinct
#print axioms subsets
#print axioms fval
#print axioms checkL1
#print axioms msl_fmz_erdos535_campaign_001_R010_L1_a1r1
