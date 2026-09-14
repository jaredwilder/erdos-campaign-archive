import Mathlib

set_option autoImplicit false


-- Exact integer model of d=1 unit-distance pairs.
-- Points are integers; a pair of points at distance exactly 1 is a unit pair.
-- On the integer line, the number of unit pairs of a sorted finite set is
-- the number of adjacent (gap-1) pairs, computable exactly in Nat.

def unitPairs (s : List Nat) : Nat :=
  match s with
  | [] => 0
  | x :: rest => (rest.map (fun y => if y - x == 1 then 1 else 0)).foldl (· + ·) 0
    + unitPairs rest

def allSortedSubsets : Nat -> Nat -> List (List Nat)
  | 0, _ => [[]]
  | _, 0 => [[]]
  | m+1, k+1 =>
      -- subsets of {0..m} of size k+1, each listed in increasing order
      (allSortedSubsets m (k+1)) ++
      ((allSortedSubsets m k).filterMap
        (fun s => match s with
          | [] => some [m]
          | x :: _ => if x > m then none else some (s ++ [m])))

def maxUnitPairs (n : Nat) : Nat :=
  (allSortedSubsets (n) n).foldl (fun m s => Nat.max m (unitPairs s)) 0

def check_upper (n : Nat) : Bool :=
  (allSortedSubsets n n).all (fun s => unitPairs s ≤ n - 1)

def check_lower (n : Nat) : Bool :=
  maxUnitPairs n == n - 1

def check_f1_5 : Bool :=
  check_upper 5 && check_lower 5 && (unitPairs [0,1,2,3,4] == 4)

theorem msl_fmz_erdos1085_campaign_001_R005_L1  : check_f1_5 = true ∧ maxUnitPairs 5 = 4 := by native_decide

-- axiom footprint
#print axioms unitPairs
#print axioms allSortedSubsets
#print axioms maxUnitPairs
#print axioms check_upper
#print axioms check_lower
#print axioms check_f1_5
#print axioms msl_fmz_erdos1085_campaign_001_R005_L1
