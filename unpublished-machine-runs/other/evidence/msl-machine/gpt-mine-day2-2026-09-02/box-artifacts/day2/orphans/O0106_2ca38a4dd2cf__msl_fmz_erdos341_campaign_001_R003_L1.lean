import Mathlib

set_option autoImplicit false


-- Canonical greedy construction with A={1}: a1=1, and for n>=1,
-- a_{n+1} = least m > a_n with m not in {a_i + a_j : i,j <= n}.
-- Fully decidable, Nat/Bool only; membership test via decidable List checks.

def isSumOfTwo {l : List Nat} (m : Nat) : Bool :=
  l.any (fun x => l.any (fun y => x + y == m))

def nextGreedy (prev : List Nat) : Nat :=
  let a := prev.getLastD 1 1
  let rec leastExcl : Nat → Nat
    | m => if isSumOfTwo (prev) m then leastExcl (m+1) else m
  leastExcl (a + 1)

def greedySeq : Nat → List Nat
  | 0 => [1]
  | (n+1) =>
    let prev := greedySeq n
    prev ++ [nextGreedy prev]

def gapsAllTwo (s : List Nat) : Bool :=
  match s with
  | [] => true
  | [_] => true
  | _ :: rest => (rest.headD 0 - s.headD 0 == 2) && gapsAllTwo rest

def checkSingleton (bound : Nat) : Bool :=
  let s := greedySeq bound
  s.all (fun a => a % 2 == 1) && gapsAllTwo s

theorem msl_fmz_erdos341_campaign_001_R003_L1  : checkSingleton 12 = true := by native_decide

-- axiom footprint
#print axioms isSumOfTwo
#print axioms nextGreedy
#print axioms greedySeq
#print axioms gapsAllTwo
#print axioms checkSingleton
#print axioms msl_fmz_erdos341_campaign_001_R003_L1
