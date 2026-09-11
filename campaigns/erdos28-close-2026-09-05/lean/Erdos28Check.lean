/-
  Erdős Problem 28 — AXIOM AUDIT.

  `#print axioms` on every theorem this campaign banks.  The expected clean footprint is
  exactly `propext, Classical.choice, Quot.sound`.  Any `sorryAx` here voids the campaign;
  `native_decide` is not used anywhere in this development.

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Erdos28Summary

namespace Erdos28

-- Core: semantic binding and the limsup translation
#print axioms Erdos28.rep_eq_sumConv
#print axioms Erdos28.rep_le_succ
#print axioms Erdos28.limsup_le_of_rep_le
#print axioms Erdos28.rep_bdd_of_limsup_ne_top
#print axioms Erdos28.limsup_eq_top_iff
#print axioms Erdos28.erdos28_iff_no_bounded_basis
#print axioms Erdos28.one_le_rep_of_basis

-- Parity: THE FLOOR
#print axioms Erdos28.swap_mem_rep_set
#print axioms Erdos28.two_le_rep_of_odd
#print axioms Erdos28.frequently_odd_atTop
#print axioms Erdos28.two_le_rep_odd_of_basis
#print axioms Erdos28.frequently_two_le_rep
#print axioms Erdos28.two_le_limsup_of_basis
#print axioms Erdos28.not_rep_le_one_of_basis
#print axioms Erdos28.two_le_bound_of_basis

-- Sandwich: the two-sided counting pin
#print axioms Erdos28.pairsLe_eq_biUnion
#print axioms Erdos28.sum_rep_eq
#print axioms Erdos28.sum_rep_le
#print axioms Erdos28.le_sum_rep
#print axioms Erdos28.basis_count
#print axioms Erdos28.cnt_sq_le_of_rep_le
#print axioms Erdos28.counterexample_sandwich
#print axioms Erdos28.counterexample_sandwich_real

-- Reduction: the structure theorem and THE KILL
#print axioms Erdos28.counterexample_structure
#print axioms Erdos28.erdos28_iff_no_theta_sqrt_basis
#print axioms Erdos28.parityAdmissible_shifted_rep
#print axioms Erdos28.parityWitness_admissible
#print axioms Erdos28.parityWitness_le_two
#print axioms Erdos28.parity_saturates_at_two
#print axioms Erdos28.parityWitness_moment
#print axioms Erdos28.parity_and_moment_saturate_at_two
#print axioms Erdos28.not_parityAdmissible_implies_three
#print axioms Erdos28.erdos28_iff_every_bound_exceeded

-- Summary
#print axioms Erdos28.campaign_state
#print axioms Erdos28.what_remains

end Erdos28
