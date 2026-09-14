set_option autoImplicit false

def artifacts : List String := []

def soundly_issued : List String -> Bool
  | [] => false
  | _ => true

def fail_closed_abort_forced : Bool :=
  artifacts.length == 0 && soundly_issued artifacts == false

theorem msl_fmz_erdos400_campaign_001_R002_L1  : fail_closed_abort_forced = true := by decide
