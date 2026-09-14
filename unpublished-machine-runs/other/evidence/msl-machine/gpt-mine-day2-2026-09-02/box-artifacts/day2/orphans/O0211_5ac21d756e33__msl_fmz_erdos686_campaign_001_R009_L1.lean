import Mathlib

set_option autoImplicit false


-- Exact rational comparison |prod_m/prod_n - N| <= bound via cross-multiplication.
-- prod_n > 0 always, so |prod_m/prod_n - N| <= bound  <=>  |prod_m - N*prod_n| <= bound*prod_n.
-- Implemented over Nat with the absolute value as max(a,b)-min(a,b) to avoid any subtlety.
def prod (s k : Nat) : Nat := (List.range k).foldl (fun acc i => acc * (s + i + 1)) 1

def residualOk (bound m n k N : Nat) : Bool :=
  let a := prod m k
  let b := N * prod n k
  let diff := max a b - min a b
  decide (diff <= bound * prod n k)

-- ACCEPT instance: N=4, k=2, m=6, n=1, bound=6.
-- prod 6 2 = 56, N * prod 1 2 = 4*6 = 24, |56-24| = 32, bound*prod_n = 36, 32 <= 36.
def check_accept : Bool := residualOk 6 6 1 2 4

-- ABORT instance: N=4, k=2, m=4, n=1, bound=0.
-- prod 4 2 = 30, N * prod 1 2 = 24, |30-24| = 6, bound*prod_n = 0, 6 <= 0 fails.
def check_abort : Bool := residualOk 0 4 1 2 4

def checkL1 : Bool := check_accept && !check_abort

theorem msl_fmz_erdos686_campaign_001_R009_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms prod
#print axioms residualOk
#print axioms check_accept
#print axioms check_abort
#print axioms checkL1
#print axioms msl_fmz_erdos686_campaign_001_R009_L1
