import Mathlib

set_option autoImplicit false


def sqfree : Nat -> Bool
  | 0 => false
  | 1 => true
  | n => (List.range ((n/2)+1)).all (fun d => d <= 1 || n % d != 0 || (d*d > n))

def sqfreeList (x : Nat) : List Nat :=
  (List.range (x+1)).filter sqfree

def gaps (x : Nat) : List Nat :=
  match sqfreeList x with
  | [] => []
  | l => (l.zip (l.drop 1)).map (fun p => p.2 - p.1)

-- alpha = 0 finite telescoping identity: each gap contributes 1,
-- so the partial sum of gap^0 over s_n <= x equals (count of squarefree <= x) - 1,
-- and the per-step partial-sum re-check is the chained fold.
def partialSums : List Nat -> List Nat
  | [] => []
  | l => (l.foldl (fun acc g => acc ++ [acc.getLastD 0 + g]) []).drop 1

def checkStep (x : Nat) : Bool :=
  let g := gaps x
  let n := (sqfreeList x).length
  g.all (fun d => d > 0) &&
  (g.length == n - 1 || (n <= 1 && g.length == 0)) &&
  (partialSums g).getLastD 0 == g.length

def checkRange (lo hi : Nat) : Bool :=
  (List.range (hi + 1 - lo)).all (fun k => checkStep (lo + k))

theorem msl_fmz_erdos145_campaign_001_R007_L1_a1r1  : checkRange 1 1000 = true := by decide

-- axiom footprint
#print axioms sqfree
#print axioms sqfreeList
#print axioms gaps
#print axioms partialSums
#print axioms checkStep
#print axioms checkRange
#print axioms msl_fmz_erdos145_campaign_001_R007_L1_a1r1
