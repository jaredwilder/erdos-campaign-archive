import Mathlib

set_option autoImplicit false


def check_k2 (N : Nat) : Bool :=
  (List.range (N+1)).all fun n =>
    (List.range (N+1)).all fun d1 =>
      (List.range (N+1)).all fun d2 =>
        d1 = 0 ∨ d2 = 0 ∨ n % d1 != 0 ∨ n % d2 != 0 ∨ d1 = d2 ∨ d1 + d2 != n
-- For every n ≤ N and every d1,d2 ≤ N: NOT (d1 ∣ n ∧ d2 ∣ n ∧ d1 ≠ d2 ∧ d1 + d2 = n).
-- This is the k=2 wing of L2: an exact disjoint 2-cover of a finite group G by
-- cosets of H1, H2 forces |G| = |H1| + |H2| with |Hi| ∣ |G| (Lagrange);
-- distinct d1,d2 ≥ 1 with d1 ∣ n, d2 ∣ n, d1 + d2 = n is impossible (each of
-- d1,d2 ≤ n/2 with equality forcing d1 = d2 = n/2), so k=2 covers with pairwise
-- distinct subgroup cardinalities cannot exist.

theorem msl_fmz_erdos274_campaign_001_R005_L2  : check_k2 20 = true := by decide

-- axiom footprint
#print axioms check_k2
#print axioms msl_fmz_erdos274_campaign_001_R005_L2
