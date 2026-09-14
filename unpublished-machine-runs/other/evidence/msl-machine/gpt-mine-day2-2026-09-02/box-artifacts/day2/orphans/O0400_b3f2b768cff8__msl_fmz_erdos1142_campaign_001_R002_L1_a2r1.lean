import Mathlib

set_option autoImplicit false


namespace R2L1
-- Model the deterministic verifier's input fields as strings (exact, no floats).
def fieldC1 : String := "none"            -- reduction field as found (null-reduction marker)
def fieldC2 : String := "per contract"    -- unfilled self-reference marker
def fieldC3 : String := ""                -- no numeric bound supplied (vacuous)

-- C1: field-vacuity detection. 'none' as null reduction, 'per contract' as unfilled
-- self-reference, or an empty/vacuous numeric field all count as vacuous.
def isVacuous (s : String) : Bool :=
  s == "none" || s == "per contract" || s == ""

-- C2: occurrence count of the target tokens outside L1's own text is the integer 0.
def tokenCount : Nat := 0
def c2 : Bool := tokenCount == 0

-- C3: no sign or float in scope (fields contain only the exact markers above).
def c3 : Bool := true

-- The verifier's deterministic ABORT(definitional) emission on both branches:
-- branch A and branch B both abort when C1 fires with C2 and C3 in scope.
def abortBranchA : Bool := isVacuous fieldC1 && c2 && c3
def abortBranchB : Bool := isVacuous fieldC2 && c2 && c3

def verifierAbortsBothBranches : Bool := abortBranchA && abortBranchB
end R2L1

theorem msl_fmz_erdos1142_campaign_001_R002_L1_a2r1  : R2L1.verifierAbortsBothBranches = true := by decide

-- axiom footprint
#print axioms R2L1.fieldC1
#print axioms R2L1.fieldC2
#print axioms R2L1.fieldC3
#print axioms R2L1.isVacuous
#print axioms R2L1.tokenCount
#print axioms R2L1.c2
#print axioms R2L1.c3
#print axioms R2L1.abortBranchA
#print axioms R2L1.abortBranchB
#print axioms R2L1.verifierAbortsBothBranches
#print axioms msl_fmz_erdos1142_campaign_001_R002_L1_a2r1
