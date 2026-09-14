import Mathlib

set_option autoImplicit false


def Ω : Nat → Nat := fun m => if m ≤ 1 then 0 else (divisorsLoop m 2) where divisorsLoop m d := if d > m then 0 else if m % d == 0 then 1 + divisorsLoop (m / d) d else divisorsLoop m (d+1)

def checkK (k n : Nat) : Bool :=
  let w := 2 ^ k
  let t := (n + w - 1) / w
  let m := w * t
  n ≤ m && m < n + w && t ≥ 2 && Ω m ≥ k + 1

def check : Bool :=
  (List.range 11).all fun i =>
    (List.range 5000).all fun j => checkK (i + 2) (j + 1)

theorem msl_fmz_erdos891_campaign_001_R009_L1_a1r1  : check = true := by native_decide

-- axiom footprint
#print axioms Ω
#print axioms checkK
#print axioms check
#print axioms msl_fmz_erdos891_campaign_001_R009_L1_a1r1
