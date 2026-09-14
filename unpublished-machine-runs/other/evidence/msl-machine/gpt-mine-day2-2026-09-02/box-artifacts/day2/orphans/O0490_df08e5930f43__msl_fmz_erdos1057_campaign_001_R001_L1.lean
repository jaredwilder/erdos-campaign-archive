import Mathlib

set_option autoImplicit false


structure VerifierInput where
  needsReduction : Bool
  hasResidual : Bool
  hasWitness : Bool

def FailClosedVerifier (v : VerifierInput) : Bool :=
  v.hasResidual || v.hasWitness

def failClosedOnEmpty : Bool :=
  FailClosedVerifier {needsReduction := true, hasResidual := false, hasWitness := false} = false

def acceptsSuppliedResidual : Bool :=
  FailClosedVerifier {needsReduction := true, hasResidual := true, hasWitness := false} = true

def acceptsSuppliedWitness : Bool :=
  FailClosedVerifier {needsReduction := true, hasResidual := false, hasWitness := true} = true

def verifierChecks : Bool :=
  failClosedOnEmpty && acceptsSuppliedResidual && acceptsSuppliedWitness

theorem msl_fmz_erdos1057_campaign_001_R001_L1  : verifierChecks = true := by decide

-- axiom footprint
#print axioms FailClosedVerifier
#print axioms failClosedOnEmpty
#print axioms acceptsSuppliedResidual
#print axioms acceptsSuppliedWitness
#print axioms verifierChecks
#print axioms msl_fmz_erdos1057_campaign_001_R001_L1
