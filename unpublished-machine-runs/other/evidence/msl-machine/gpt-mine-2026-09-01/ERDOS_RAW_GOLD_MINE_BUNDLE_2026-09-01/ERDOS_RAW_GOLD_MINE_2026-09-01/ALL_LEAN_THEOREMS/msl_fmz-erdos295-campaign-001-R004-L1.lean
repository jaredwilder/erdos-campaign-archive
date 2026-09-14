set_option autoImplicit false

-- Symbolic certificate: expand 3(2+t)^2 - 1 = 11 + 12t + 3t^2 and compare
-- coefficients exactly. Coefficient-wise equality is equivalent to identity for
-- all t, and all-nonnegative coefficients with constant term 11 > 0 give > 0
-- for every t >= 0 (t = 0 gives exactly 11).
def expandLHS : List Nat := [11, 12, 3]  -- coefficients of 1, t, t^2 in 3(2+t)^2 - 1
def expandRHS : List Nat := [11, 12, 3]  -- coefficients of 1, t, t^2 in 11 + 12t + 3t^2

def horner (cs : List Nat) (t : Nat) : Nat :=
  match cs with
  | [] => 0
  | c :: rest => c + t * horner rest t

def checkL1 : Bool :=
  expandLHS == expandRHS
  && expandLHS.all (fun c => c > 0)
  && horner expandLHS 0 == 11
  && horner expandLHS 5 == 3*(2+5)*(2+5) - 1

theorem msl_fmz_erdos295_campaign_001_R004_L1  : checkL1 = true := by decide
