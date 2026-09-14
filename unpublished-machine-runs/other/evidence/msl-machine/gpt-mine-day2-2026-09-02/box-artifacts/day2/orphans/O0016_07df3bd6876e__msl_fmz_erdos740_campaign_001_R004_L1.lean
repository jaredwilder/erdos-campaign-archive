import Mathlib

set_option autoImplicit false


-- Finite checkable fragment of L1: the supplied R004 input record
-- carries no numerical claim to verify. Encode the input descriptor as a
-- finite record of (field, value) string pairs, exactly as supplied by the
-- orchestrator, and define a total Bool-valued verifier that fails closed:
-- it returns true only if (a) the analytic reduction field is exactly "none",
-- (b) the residual claim field is exactly "per contract", and (c) no field
-- of the record is a numerical claim (i.e. every field name is one of the
-- three declared non-numeric fields). Any unknown field => false.

structure R004Input where
  analytic_reduction : String
  residual_claim : String
  extra_fields : List String

def declaredNonNumericFields : List String :=
  ["analytic_reduction", "residual_claim", "aux_note"]

def isNumericClaimField (s : String) : Bool :=
  !(declaredNonNumericFields.contains s)

def checkNoNumericalClaim (r : R004Input) : Bool :=
  r.analytic_reduction == "none"
    && r.residual_claim == "per contract"
    && !(r.extra_fields.any isNumericClaimField)

-- The actual supplied inputs for R004/L1, as recorded by the orchestrator:
def suppliedInput : R004Input :=
  { analytic_reduction := "none"
    residual_claim := "per contract"
    extra_fields := ["aux_note"] }

def L1_fragment_check : Bool := checkNoNumericalClaim suppliedInput

theorem msl_fmz_erdos740_campaign_001_R004_L1  : L1_fragment_check = true := by decide

-- axiom footprint
#print axioms declaredNonNumericFields
#print axioms isNumericClaimField
#print axioms checkNoNumericalClaim
#print axioms suppliedInput
#print axioms L1_fragment_check
#print axioms msl_fmz_erdos740_campaign_001_R004_L1
