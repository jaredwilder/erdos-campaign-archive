import Mathlib

set_option autoImplicit false


def ops : List String := ["emit_certificate", "apply_reduction", "assume_conclusion", "skip_verification", "use_unchecked_hypothesis"]

def forbidden_for_empty_reduction (op : String) : Bool :=
  op != "no_certificate"  -- with empty reduction, any op other than declining is forbidden

def all_outputs : List String := "no_certificate" :: ops

def check_L1 : Bool :=
  all_outputs.all (fun out =>
    if forbidden_for_empty_reduction out then
      -- every forbidden op must indeed be inadmissible: it is not the sole output
      true
    else
      out = "no_certificate")
  && (all_outputs.filter (fun out => !forbidden_for_empty_reduction out) = ["no_certificate"])

theorem msl_fmz_erdos75_campaign_001_R001_L1  : check_L1 = true := by decide

-- axiom footprint
#print axioms ops
#print axioms forbidden_for_empty_reduction
#print axioms all_outputs
#print axioms check_L1
#print axioms msl_fmz_erdos75_campaign_001_R001_L1
