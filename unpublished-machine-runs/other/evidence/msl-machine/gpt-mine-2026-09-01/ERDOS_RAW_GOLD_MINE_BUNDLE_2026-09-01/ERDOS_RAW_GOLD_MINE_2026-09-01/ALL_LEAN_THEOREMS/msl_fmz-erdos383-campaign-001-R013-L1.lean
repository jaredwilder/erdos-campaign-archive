set_option autoImplicit false

def divisorsLeq (n p : Nat) : Bool :=
  (List.range (n + 1)).filter (fun d => d > 0 /\ n % d == 0) |>.all (fun d => d <= p)

def auxFactorsLeq (p k : Nat) : Bool :=
  (List.range (k + 1)).all (fun i => divisorsLeq (p*p + i) p)

def checkUnpacking (p k : Nat) : Bool :=
  auxFactorsLeq p k

theorem msl_fmz_erdos383_campaign_001_R013_L1  : checkUnpacking 2 2 = true /\ checkUnpacking 3 1 = true /\ checkUnpacking 5 0 = true /\ checkUnpacking 7 3 = false := by decide
