import Mathlib

set_option autoImplicit false



def Sqf (k : Nat) : Bool :=
  k ≥ 1 ∧ ∀ d, 2 ≤ d → d * d ≤ k → k % d ≠ 0

def good (n l : Nat) : Bool := 2^l < n && Sqf (n - 2^l)

def oddUpTo (lo hi : Nat) : List Nat :=
  (List.range ((hi - lo) / 2 + 1)).map (fun i => lo + 2*i)

def checkList (ns : List Nat) : Bool := ns.all (fun n => (List.range 8).any (fun l => good n l))

def check_witness : Bool := checkList (oddUpTo 3 255)

theorem msl_fmz_erdos11_campaign_001_R007_L1  : check_witness = true ∧ Sqf 57 = true ∧ good 185 7 = true := by decide

-- axiom footprint
#print axioms Sqf
#print axioms good
#print axioms oddUpTo
#print axioms checkList
#print axioms check_witness
#print axioms msl_fmz_erdos11_campaign_001_R007_L1
