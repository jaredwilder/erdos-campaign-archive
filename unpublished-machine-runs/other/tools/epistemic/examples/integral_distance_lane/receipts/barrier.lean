/- This receipt documents that a former sorry-shaped gap is absent. -/
theorem bounded_coordinate_barrier (reachable required : Nat)
    (hReach : reachable ≤ 100) (hNeed : 15700 ≤ required) : reachable < required := by
  omega
