import Mathlib

set_option autoImplicit false


def gc : Nat -> Nat -> Nat
  | 0, m => m
  | (Nat.succ k), m => gc (m % (k+1)) (k+1)

/-- Condition defining f_3: a set s is ADMISSIBLE iff no 3-element subset
has all three pairwise gcds equal (i.e. no triple with
gcd(a,b)=gcd(a,c)=gcd(b,c)). --/
def noBadTriple (s : List Nat) : Bool :=
  ((List.range s.length).flatMap fun i =>
    (List.range s.length).flatMap fun j =>
      (List.range s.length).filterMap fun k =>
        if i < j && j < k then
          some (gc (s.getD i 0) (s.getD j 0) == gc (s.getD i 0) (s.getD k 0)
             && gc (s.getD i 0) (s.getD k 0) == gc (s.getD j 0) (s.getD k 0))
        else none).any (fun b => b) == false

def allSubsets : List Nat -> List (List Nat)
  | [] => [[]]
  | x :: xs => let rest := allSubsets xs
               rest ++ rest.map (fun t => x :: t)

def f3val (n : Nat) : Nat :=
  (allSubsets (List.range' 1 n)).filter noBadTriple
    |>.foldl (fun acc s => Nat.max acc s.length) 0

def witnessOk : Bool := noBadTriple [1,3] && noBadTriple [1,2,4]

def checkL1 : Bool :=
  f3val 3 == 2 && f3val 4 == 3 && f3val 5 == 3 && f3val 6 == 3 && witnessOk

theorem msl_fmz_erdos535_campaign_001_R010_L1_a1r2  : checkL1 = true := by native_decide

-- axiom footprint
#print axioms gc
#print axioms noBadTriple
#print axioms allSubsets
#print axioms f3val
#print axioms witnessOk
#print axioms checkL1
#print axioms msl_fmz_erdos535_campaign_001_R010_L1_a1r2
