import Mathlib

set_option autoImplicit false

namespace Day2Wrap



import-free Nat/Bool core; no Rat, no native_decide.

The gap-second-moment check is lifted to integers: for a Sidon set A with
t = |A+A|, Q(A) >= 2  <=>  (t-1) * Sum (s_{i+1}-s_i)^2 >= 2 * (t-1)^2,
an exact Nat inequality, so `decide`-style Bool evaluation on Nat suffices.

-- exact sumset (distinct sums, matching the canonical t = |A+A|)
def sumset (A : List Nat) : List Nat :=
  (A.flatMap (fun a => A.map (fun b => a + b))).eraseDups

def tOf (A : List Nat) : Nat := (sumset A).length

def gapSqSum (A : List Nat) : Nat :=
  let s := A.mergeSort (fun x y => x <= y)
  match s with
  | [] => 0
  | x :: xs => xs.foldl (fun acc y => acc + (y - x) * (y - x)) 0
    -- NOTE: replaced below by an explicit pairwise version to be exact

def gapSq (A : List Nat) : Nat :=
  let s := A.mergeSort (fun x y => x <= y)
  (List.zip (s.dropLast) (s.drop 1)).foldl
    (fun acc p => acc + (p.2 - p.1) * (p.2 - p.1)) 0

def lhs (A : List Nat) : Nat :=
  let t := tOf A
  (t - 1) * gapSq A

def rhs (A : List Nat) : Nat :=
  let t := tOf A
  2 * (t - 1) * (t - 1)

def isSortedStrict (A : List Nat) : Bool :=
  match A with
  | [] => true
  | x :: xs => xs.all (fun y => x < y) && isSortedStrict xs

def isSidon (A : List Nat) : Bool :=
  let pairs := A.flatMap (fun a => A.map (fun b => (a, b)))
  pairs.all (fun p => pairs.all (fun q =>
    p.1 + p.2 == q.1 + q.2 -> (p.1 == q.1 && p.2 == q.2 || p.1 == q.2 && p.2 == q.1)))

def isMin0 (A : List Nat) : Bool := A.head? == some 0

-- full enumeration: all 715 strictly increasing 4-subsets of [0,12]
def dom : List Nat := List.range 13

def sub4 : List (List Nat) :=
  dom.flatMap fun a => dom.flatMap fun b => dom.flatMap fun c => dom.flatMap fun d =>
    if a < b && b < c && c < d then [[a, b, c, d]] else []

def ok (A : List Nat) : Bool :=
  isSortedStrict A && isSidon A && isMin0 A -> lhs A >= rhs A

def check_all : Bool := sub4.all ok

def extremizer_ok : Bool :=
  isSidon [0,1,4,6] && isMin0 [0,1,4,6] && lhs [0,1,4,6] == rhs [0,1,4,6]

def check_L1_core : Bool := check_all && extremizer_ok

theorem msl_fmz_erdos153_campaign_001_R006_L1_a1r2  : check_L1_core = true := by decide

end Day2Wrap
-- axiom footprint
#print axioms Day2Wrap.sumset
#print axioms Day2Wrap.tOf
#print axioms Day2Wrap.gapSqSum
#print axioms Day2Wrap.gapSq
#print axioms Day2Wrap.lhs
#print axioms Day2Wrap.rhs
#print axioms Day2Wrap.isSortedStrict
#print axioms Day2Wrap.isSidon
#print axioms Day2Wrap.isMin0
#print axioms Day2Wrap.dom
#print axioms Day2Wrap.sub4
#print axioms Day2Wrap.ok
#print axioms Day2Wrap.check_all
#print axioms Day2Wrap.extremizer_ok
#print axioms Day2Wrap.check_L1_core
#print axioms Day2Wrap.msl_fmz_erdos153_campaign_001_R006_L1_a1r2
