import Mathlib

set_option autoImplicit false


def sums (S : List Nat) : List Nat := S.flatMap (fun a => S.map (fun b => a + b))

def inSums (x : Nat) (S : List Nat) : Bool :=(sums S).contains x

def nextEl (S : List Nat) (cur : Nat) : Nat :=
  let rec go (x fuel : Nat) : Nat :=
    match fuel with
    | 0 => x
    | Nat.succ f => if inSums x S then go (x+1) f else x
  go (cur+1) (cur+2)

def buildSeq (A : List Nat) (n : Nat) : List Nat :=
  let rec go (S : List Nat) (k : Nat) : List Nat :=
    match k with
    | 0 => S
    | Nat.succ f => go (S ++ [nextEl S (match S.getLast? with | some x => x | none => 0)]) f
  go A n

def gaps (L : List Nat) : List Nat :=
  match L with
  | [] => []
  | x :: xs => xs.zipWith (fun a b => b - a) (x :: xs)

/-- Check: gaps of the greedy extension of A are p-periodic from index N0 on,
    verified over a window of w full periods. --/
def checkCert (A : List Nat) (p N0 w : Nat) : Bool :=
  let L := buildSeq A (N0 + 2 * p * w + 2)
  let g := gaps L
  List.all (List.range (p * w)) (fun i =>
    match g.getD (N0 + i)? 0, g.getD (N0 + i + p)? 0 with
    | a, b => a == b && a != 0)

theorem msl_fmz_erdos341_campaign_001_R005_T1_a1r1  : checkCert [1] 1 1 3 = true := by decide

-- axiom footprint
#print axioms sums
#print axioms inSums
#print axioms nextEl
#print axioms buildSeq
#print axioms gaps
#print axioms checkCert
#print axioms msl_fmz_erdos341_campaign_001_R005_T1_a1r1
