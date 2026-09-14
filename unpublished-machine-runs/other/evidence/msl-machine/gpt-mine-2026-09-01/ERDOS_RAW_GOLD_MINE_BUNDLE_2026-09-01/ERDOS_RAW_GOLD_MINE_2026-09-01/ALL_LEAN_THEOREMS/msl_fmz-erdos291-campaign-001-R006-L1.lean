set_option autoImplicit false

def check : Bool :=
  let x : Nat := (2*6 + 1*6 - 3*6)
  let d : Nat := 36
  let n2 : Nat := 2*36 + 1*36 - 3*36
  (x == 0) && (n2 == 0) && (d == 36)

theorem msl_fmz_erdos291_campaign_001_R006_L1  : check = true := by decide
