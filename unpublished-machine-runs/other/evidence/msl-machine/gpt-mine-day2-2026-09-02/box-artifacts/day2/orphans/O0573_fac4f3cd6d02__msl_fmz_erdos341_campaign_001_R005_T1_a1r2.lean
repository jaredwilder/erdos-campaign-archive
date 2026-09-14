import Mathlib

set_option autoImplicit false


-- is x a sum of two elements of S?
def inSums (x : Nat) (S : List Nat) : Bool :=
  (S.flatMap (fun a => S.map (fun b => a + b))).contains x

-- least integer > cur not in sums(S), with fuel
def nextEl (x fuel cur : Nat) (S : List Nat) : Nat :=
  match fuel with
  | 0 => x
  | Nat.succ f => if inSums x S then nextEl (x+1) f cur S else x

-- greedy extension of A to total length n (append n - A.length elements)
def extend (A : List Nat) (k : Nat) : List Nat :=
  match k with
  | 0 => A
  | Nat.succ f =>
      let L := extend A f
      let cur := match L.getLast? with | some x => x | none => 0
      L ++ [nextEl (cur+1) (cur+2) cur L]

def buildSeq (A : List Nat) (n : Nat) : List Nat :=
  extend A n

-- consecutive gaps
def gaps (L : List Nat) : List Nat :=
  match L with
  | [] => []
  | x :: xs =>
      (xs.zip (x :: xs)).map (fun pr => match pr with | (b, a) => b - a)

/-- Check: gaps of the greedy extension of A are p-periodic from index N0,
    over w full periods; every compared gap must be nonzero. --/
def checkCert (A : List Nat) (p N0 w : Nat) : Bool :=
  let L := buildSeq A (N0 + 2 * p * w + 2)
  let g := gaps L
  (List.range (p * w)).all (fun i =>
    let a := g.getD (N0 + i) 0
    let b := g.getD (N0 + i + p) 0
    (a == b) && (a != 0))

theorem msl_fmz_erdos341_campaign_001_R005_T1_a1r2  : checkCert [1] 1 1 3 = true := by decide

-- axiom footprint
#print axioms inSums
#print axioms nextEl
#print axioms extend
#print axioms buildSeq
#print axioms gaps
#print axioms checkCert
#print axioms msl_fmz_erdos341_campaign_001_R005_T1_a1r2
