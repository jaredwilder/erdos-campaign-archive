import Mathlib

set_option autoImplicit false


def floorFifth (k : Nat) : Nat :=
  -- max { m : m^5 <= k^6 }, computable by bounded search (k^{6/5} >= k, so bound k+1 suffices)
  (List.range (k+2)).filter (fun m => m^5 <= k^6) |>.foldl max 0

def checkL2 (N : Nat) : Bool :=
  -- For all 1 <= k <= n <= N: (n-k+1)^5 > k^6  <->  n-k+1 >= floorFifth k + 1
  (List.range (N+1)).all (fun n =>
    (List.range (n+1)).all (fun k =>
      let t := n - k + 1
      Bool.not (Nat.ble k 0) || (decide (t^5 > k^6) == decide (t >= floorFifth k + 1))))

theorem msl_fmz_erdos683_campaign_001_R001_L2  : checkL2 60 = true := by decide

-- axiom footprint
#print axioms floorFifth
#print axioms checkL2
#print axioms msl_fmz_erdos683_campaign_001_R001_L2
