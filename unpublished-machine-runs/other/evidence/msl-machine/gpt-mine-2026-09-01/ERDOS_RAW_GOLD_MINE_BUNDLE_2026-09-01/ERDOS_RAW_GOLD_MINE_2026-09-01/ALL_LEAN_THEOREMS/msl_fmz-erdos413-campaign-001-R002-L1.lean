set_option autoImplicit false

-- distinct prime factor count computed by explicit divisibility checks,
-- no recursion, total and concrete
def d30 : Nat :=
  [2,3,5,7,11,13,17,19,23,29].filter (fun p => 30 % p == 0) |>.length

def d42 : Nat :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41].filter (fun p => 42 % p == 0) |>.length

checkL1 : Bool :=
  30 = 2 * 3 * 5 ∧ 42 = 2 * 3 * 7 ∧ d30 = 3 ∧ d42 = 3 ∧ d30 > 2 ∧ d42 > 2

theorem msl_fmz_erdos413_campaign_001_R002_L1  : checkL1 = true := by decide
