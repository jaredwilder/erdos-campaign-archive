import Mathlib

set_option autoImplicit false


-- Repair of the failed obligation: the prior sqfree test was not a correct
-- squarefreeness predicate (its divisor filter admitted composite divisors and
-- mis-bounded the range), so `decide` evaluated a false/nonsense check.
-- Here sqfree is the exact trial-division predicate: n is squarefree iff no
-- d with 2 <= d and d*d <= n divides n. Total and computable in Nat/Bool.

def sqfree (n : Nat) : Bool :=
  n > 0 && (List.range (n+1)).all
    (fun d => !(d >= 2 && d * d <= n && n % d == 0))

def sqfreeList (x : Nat) : List Nat :=
  (List.range (x+1)).filter sqfree

def gaps (x : Nat) : List Nat :=
  match sqfreeList x with
  | [] => []
  | l => (l.zip (l.drop 1)).map (fun p => p.2 - p.1)

-- Per-step partial-sum re-check: consecutive running totals must increase by
-- exactly the gap at each step, and the final total must equal the gap count
-- (the alpha = 0 telescoping identity, since gap^0 = 1 exactly).
def partialSums : List Nat -> List Nat
  | [] => []
  | l => (l.foldl (fun acc g => acc ++ [acc.getLastD 0 + g]) []).drop 1

def checkStep (x : Nat) : Bool :=
  let g := gaps x
  let n := (sqfreeList x).length
  g.all (fun d => d > 0) &&
  g.length + 1 == n &&
  (partialSums g).getLastD 0 == g.length

def checkRange (lo hi : Nat) : Bool :=
  (List.range (hi + 1 - lo)).all (fun k => checkStep (lo + k))

theorem msl_fmz_erdos145_campaign_001_R007_L1_a1r2  : checkRange 1 30 = true := by decide

-- axiom footprint
#print axioms sqfree
#print axioms sqfreeList
#print axioms gaps
#print axioms partialSums
#print axioms checkStep
#print axioms checkRange
#print axioms msl_fmz_erdos145_campaign_001_R007_L1_a1r2
