import Mathlib

set_option autoImplicit false


def coversY (n : Nat) (f : List Nat) (Y : Nat) : Bool :=
  (List.range n).all (fun x =>
    (List.range (2^n)).any (fun s => Nat.land s Y == s && f.getD s 0 == x))

def badMax (n : Nat) (f : List Nat) : Nat :=
  ((List.range (2^n)).filter (fun Y => !(coversY n f Y))).foldl (fun acc Y => max acc Y.popcount) 0

def allFns (n : Nat) : Nat -> List (List Nat)
  | 0 => [[]]
  | k+1 => (allFns n k).flatMap (fun p => (List.range n).map (fun v => v :: p))

def Hval (n : Nat) : Nat :=
  (allFns n (2^n)).foldl (fun acc f => min acc (badMax n f + 1)) (2^n)

def checkBound (n : Nat) : Bool :=
  let h := Hval n
  2^h >= n && h <= Nat.log2 n + 2

theorem msl_fmz_erdos624_campaign_001_R006_L1  : checkBound 1 = true ∧ checkBound 2 = true := by decide

-- axiom footprint
#print axioms coversY
#print axioms badMax
#print axioms allFns
#print axioms Hval
#print axioms checkBound
#print axioms msl_fmz_erdos624_campaign_001_R006_L1
