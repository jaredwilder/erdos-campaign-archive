import Mathlib

set_option autoImplicit false


def rich_line_bound (n : Nat) : Nat := n * (n - 1) / 12
def check_trivial_bound : Bool :=
  (List.range 100).all (fun n => rich_line_bound n ≤ n * n)

theorem msl_fmz_erdos101_campaign_001_R004_L1  : check_trivial_bound = true := by decide

-- axiom footprint
#print axioms rich_line_bound
#print axioms check_trivial_bound
#print axioms msl_fmz_erdos101_campaign_001_R004_L1
