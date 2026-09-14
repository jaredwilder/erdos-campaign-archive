import Mathlib

set_option autoImplicit false


def powset : List Nat → List (List Nat)
  | [] => [[]]
  | a :: as => powset as ++ (powset as).map (fun l => a :: l)

def diffs (A : List Nat) : List Nat :=
  A.flatMap (fun a => A.map (fun b => a - b))

def covers (A : List Nat) (N : Nat) : Bool :=
  (List.range N).all (fun k => (k + 1) ∈ diffs A)

def Fval (N : Nat) : Nat :=
  (powset (List.range (N + 1))).filter (fun A => covers A N)
    |>.map List.length |>.foldl min (N + 2)

def cnt (t : Nat) : Nat := t * (t - 1) / 2

def tmin (N : Nat) : Nat :=
  ((List.range (N + 2)).filter (fun t => cnt t ≥ N)).head!

def checkTiny : Bool :=
  (List.range 7).all (fun i =>
    let N := i + 1
    Fval N == tmin N)

theorem msl_fmz_erdos170_campaign_001_R006_L_tiny  : checkTiny = true ∧ Fval 1 = 2 ∧ Fval 2 = 3 ∧ Fval 3 = 3 ∧ Fval 4 = 4 ∧ Fval 5 = 4 ∧ Fval 6 = 4 ∧ Fval 7 = 5 := by decide

-- axiom footprint
#print axioms powset
#print axioms diffs
#print axioms covers
#print axioms Fval
#print axioms cnt
#print axioms tmin
#print axioms checkTiny
#print axioms msl_fmz_erdos170_campaign_001_R006_L_tiny
