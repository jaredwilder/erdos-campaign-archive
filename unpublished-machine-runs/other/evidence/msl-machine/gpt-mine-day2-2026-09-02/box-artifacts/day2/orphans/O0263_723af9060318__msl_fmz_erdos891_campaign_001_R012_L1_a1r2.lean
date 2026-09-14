import Mathlib

set_option autoImplicit false


def multiplesIn (P n : Nat) : List Nat :=
  (List.range P).filterMap (fun j =>
    let m := n + j
    if m % P == 0 then some m else none)

def windowOK (P n : Nat) : Bool :=
  (multiplesIn P n).all (fun m => P * 2 <= m)

def windowUnique (P n : Nat) : Bool :=
  (multiplesIn P n).length == 1

def checkRange (P lo count : Nat) : Bool :=
  (List.range count).all (fun i =>
    windowOK P (lo + i) && windowUnique P (lo + i))

theorem msl_fmz_erdos891_campaign_001_R012_L1_a1r2  : checkRange 6 7 100 = true ∧ checkRange 30 31 100 = true := by decide

-- axiom footprint
#print axioms multiplesIn
#print axioms windowOK
#print axioms windowUnique
#print axioms checkRange
#print axioms msl_fmz_erdos891_campaign_001_R012_L1_a1r2
