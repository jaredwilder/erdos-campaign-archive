import Mathlib

set_option autoImplicit false


inductive ExprKind | rationalExpr | parameterDomain | other deriving DecidableEq, Repr

structure RegistryEntry where
  contractSHA : Nat
  exprKind : ExprKind
  deriving Repr

def shaOfContract : Nat := 13199589280805565

-- SHA b54d25e10e8e6d8d as a Nat (hex b54d25e10e8e6d8d = 13199589280805565)

def providesRationalOrDomain (e : RegistryEntry) : Bool :=
  e.contractSHA == shaOfContract &&
    (e.exprKind == ExprKind.rationalExpr || e.exprKind == ExprKind.parameterDomain)

def checkAbort : Bool :=
  -- Artifact registry on file for route R006 as of this round: empty list.
  let registry : List RegistryEntry := []
  -- Fail-closed abort fires iff NO entry binds the contract SHA to an
  -- exact rational expression or parameter domain for the cos-comparison quantity:
  !(registry.any providesRationalOrDomain)

def checkAbortSucceeds : Prop := checkAbort = true

instance : Decidable checkAbortSucceeds := inferInstanceAs (Decidable (checkAbort = true))

theorem msl_fmz_erdos510_campaign_001_R006_L1  : checkAbortSucceeds := by decide

-- axiom footprint
#print axioms shaOfContract
#print axioms providesRationalOrDomain
#print axioms checkAbort
#print axioms checkAbortSucceeds
#print axioms msl_fmz_erdos510_campaign_001_R006_L1
