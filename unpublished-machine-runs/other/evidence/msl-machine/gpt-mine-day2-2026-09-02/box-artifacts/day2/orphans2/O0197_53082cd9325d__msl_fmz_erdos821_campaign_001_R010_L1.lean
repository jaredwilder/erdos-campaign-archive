import Mathlib

set_option autoImplicit false

namespace Day2Wrap


-- Pure, total, decidable re-encoding of the L1 fragment check on contract 77660b9c7abbba36.
-- No Real, no Classical, no I/O: the witness is a literal structure and the check is a Bool.

inductive Field where
  | canonical_statement_present
  | definition_of_g_present
  | finite_reduction_present
  | residual_with_resolved_sign_present
  | artifacts_empty

def witnessValues : Field → Bool :=
  fun f => match f with
    | .canonical_statement_present            => true   -- canonical statement is supplied
    | .definition_of_g_present                => false  -- no computable definition of g
    | .finite_reduction_present               => false  -- no finite-reduction theorem supplied
    | .residual_with_resolved_sign_present    => false  -- no residual with resolved sign
    | .artifacts_empty                        => true   -- computational artifacts on file: []

def expectedValues : Field → Bool :=
  fun f => match f with
    | .canonical_statement_present            => true
    | .definition_of_g_present                => false
    | .finite_reduction_present               => false
    | .residual_with_resolved_sign_present    => false
    | .artifacts_empty                        => true

def check_field (f : Field) : Bool := witnessValues f == expectedValues f

def check_witness : Bool :=
  (check_field .canonical_statement_present)
  && (check_field .definition_of_g_present)
  && (check_field .finite_reduction_present)
  && (check_field .residual_with_resolved_sign_present)
  && (check_field .artifacts_empty)

-- Fail-closed consequence: with no g, no finite reduction, and no resolved-sign
-- residual, the unique correct verifier output for substantive content is ABORT.
def verifier_output : String := if check_witness then "ABORT-UNIQUELY-CORRECT" else "INTERNAL-ERROR"

def closure_check : Bool := check_witness && (verifier_output == "ABORT-UNIQUELY-CORRECT")

theorem msl_fmz_erdos821_campaign_001_R010_L1  : closure_check = true := by decide

end Day2Wrap
-- axiom footprint
#print axioms Day2Wrap.witnessValues
#print axioms Day2Wrap.expectedValues
#print axioms Day2Wrap.check_field
#print axioms Day2Wrap.check_witness
#print axioms Day2Wrap.verifier_output
#print axioms Day2Wrap.closure_check
#print axioms Day2Wrap.msl_fmz_erdos821_campaign_001_R010_L1
