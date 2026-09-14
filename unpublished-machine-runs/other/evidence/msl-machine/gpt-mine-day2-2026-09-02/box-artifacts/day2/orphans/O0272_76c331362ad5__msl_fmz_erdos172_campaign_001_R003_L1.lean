import Mathlib

set_option autoImplicit false


inductive Reduction where
  | none : Reduction

/-- The set of residual expressions produced by a reduction, as a finite list.
    Under reduction "none" no rewriting rule applies, so the residual set is empty.
    This is the decidable core of L1: the residual list is literally [], hence no
    exact/outward certificate can be constructed from it. -/
def residuals : Reduction → List String
  | Reduction.none => []

/-- Certification of a residual list: an exact/outward certificate exists iff the
    residual list is nonempty (a residual expression is what gets certified outward).
    Fail-closed means: empty residual list ⇒ certification returns false. -/
def certifiable (rs : List String) : Bool :=
  match rs with
  | [] => false
  | _ => true

/-- The full fail-closed check for reduction "none":
    (1) the residual set is empty, and (2) certification of it fails. -/
def check_L1 : Bool :=
  residuals Reduction.none = [] && certifiable (residuals Reduction.none) = false

theorem msl_fmz_erdos172_campaign_001_R003_L1  : check_L1 = true := by decide

-- axiom footprint
#print axioms residuals
#print axioms certifiable
#print axioms check_L1
#print axioms msl_fmz_erdos172_campaign_001_R003_L1
