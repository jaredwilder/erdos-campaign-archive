import Mathlib

set_option autoImplicit false


def S : List Nat := [1]

def isSumFreePt (S : List Nat) (a b : Nat) : Bool :=
  !S.contains ((a + b) % 7)

def goodA (S : List Nat) (A : List Nat) : Bool :=
  A.all (fun a => !S.contains a) &&
  A.all (fun a => A.all (fun b => isSumFreePt S a b))

def subsets (l : List Nat) : List (List Nat) :=
  match l with
  | [] => [[]]
  | x :: r => (subsets r) ++ (subsets r).map (fun s => x :: s)

def check_R010 : Bool :=
  (subsets ((List.range 7).filter (fun n => !S.contains n))).any (goodA S)

theorem msl_fmz_erdos949_campaign_001_R010_L1  : check_R010 = true := by decide

-- axiom footprint
#print axioms S
#print axioms isSumFreePt
#print axioms goodA
#print axioms subsets
#print axioms check_R010
#print axioms msl_fmz_erdos949_campaign_001_R010_L1
