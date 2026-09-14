import Mathlib

set_option autoImplicit false


def probe_p3_n2_candidates : List Nat := [3]
def probe_p3_n2_check : Bool :=
  probe_p3_n2_candidates.all (fun a => (a * a) % 3 != 1)

def in_interval : Prop := (2 : Nat) < 3 /\ 3 < 2 + 2
-- 3^{c} for c in (1/2, log_3 2) lies in (sqrt 3, 2), so (n, n+3^c) = (2, 2+3^c)
-- contains exactly the integers a = 3 (since 2 < 3 < 2 + sqrt(3) < 4 <= 2 + 3^c upper
-- is in (2+sqrt3, 4)); a = 4 is excluded because 3^c < 2 for c < log_3 2.

theorem msl_fmz_erdos445_campaign_001_R001_L1  : probe_p3_n2_check = true := by decide

-- axiom footprint
#print axioms probe_p3_n2_candidates
#print axioms probe_p3_n2_check
#print axioms in_interval
#print axioms msl_fmz_erdos445_campaign_001_R001_L1
