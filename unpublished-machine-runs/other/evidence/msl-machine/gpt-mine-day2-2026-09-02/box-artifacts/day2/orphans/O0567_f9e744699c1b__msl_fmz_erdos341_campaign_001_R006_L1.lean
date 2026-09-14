import Mathlib

set_option autoImplicit false


def isSum (s : List Nat) (k : Nat) : Bool :=
  (s.flatMap (fun a => s.map (fun b => a + b))).contains k

def findNext (s : List Nat) : Nat -> Nat -> Nat
  | 0, _ => 0
  | fuel+1, k => if isSum s k then findNext s fuel (k+1) else k

def build : Nat -> List Nat
  | 0 => [1]
  | n+1 =>
      let s := build n
      s ++ [findNext s 200 (s.getLast! + 1)]

def gapsAreTwo (l : List Nat) : Bool :=
  match l with
  | [] | [_] => true
  | a :: b :: rest => (b - a == 2) && gapsAreTwo (b :: rest)

def check (n : Nat) : Bool :=
  let l := build n
  l.all (fun a => a % 2 == 1) && gapsAreTwo l

theorem msl_fmz_erdos341_campaign_001_R006_L1  : check 12 = true := by decide

-- axiom footprint
#print axioms isSum
#print axioms findNext
#print axioms build
#print axioms gapsAreTwo
#print axioms check
#print axioms msl_fmz_erdos341_campaign_001_R006_L1
