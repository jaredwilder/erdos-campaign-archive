import Mathlib

set_option autoImplicit false


def covers (A : List Nat) (N : Nat) : Bool :=
  (List.range (N+1)).all (fun k => A.any (fun a => A.any (fun b => a = b + k)))

def subsets : List Nat -> Nat -> List (List Nat)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: rest, s + 1 =>
      (subsets rest s).map (fun t => x :: t) ++ subsets rest (s+1)

def existsCoverOfSize (N s : Nat) : Bool :=
  (subsets (List.range (N+1)) s).any (fun A => covers A N)

def fValue (N : Nat) : Nat :=
  ((List.range (N+2)).filter (fun s => existsCoverOfSize N s)).head!

def f10 : Nat := fValue 10

theorem msl_fmz_erdos170_campaign_001_R007_L1  : f10 = 6 := by decide

-- axiom footprint
#print axioms covers
#print axioms subsets
#print axioms existsCoverOfSize
#print axioms fValue
#print axioms f10
#print axioms msl_fmz_erdos170_campaign_001_R007_L1
