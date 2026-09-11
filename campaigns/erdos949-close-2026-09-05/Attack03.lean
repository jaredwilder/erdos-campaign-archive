import Mathlib
import Attack01

/-!
# Erdős 949 — sharpening the measure branch to INNER measure

`Attack01.witness_of_measurable_pos` needs `S` itself to be measurable. That is wasteful:
Steinhaus only has to be applied to a measurable subset, because the lever
`S ∩ (S - S) = ∅` is monotone in the subset. So:

* `witness_of_measurable_subset_pos` : if a sum-free `S` merely CONTAINS a measurable set of
  positive measure (i.e. `S` has positive inner Lebesgue measure), the conclusion of
  Erdős 949 holds for `S`, and `S` is bounded away from `0`.

Consequence for the open problem: a counterexample must have **inner measure zero**
(every measurable subset null) while having positive outer measure — a Vitali-like,
saturated-non-measurable shape — and must accumulate at `0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Cardinal MeasureTheory
open scoped Pointwise Cardinal Topology

namespace Erdos949Close

variable {S : Set ℝ}

/-- If a sum-free `S` contains a measurable set of positive measure, it is bounded away
from the origin. -/
theorem gap_of_measurable_subset_pos (hSF : SumFree S) {S₀ : Set ℝ} (hsub : S₀ ⊆ S)
    (hm : MeasurableSet S₀) (hpos : 0 < volume S₀) : ∃ ε > 0, Ioo (-ε) ε ⊆ Sᶜ := by
  have hst : S₀ - S₀ ∈ 𝓝 (0 : ℝ) :=
    MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos volume S₀ hm hpos
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hst
  refine ⟨ε, hε, fun x hx => ?_⟩
  have hxb : x ∈ Metric.ball (0 : ℝ) ε := by
    rw [Real.ball_eq_Ioo]
    simpa using hx
  have hmono : S₀ - S₀ ⊆ S - S := Set.sub_subset_sub hsub hsub
  exact sub_subset_compl hSF (hmono (hball hxb))

/-- **Positive inner measure suffices.** A sum-free `S` containing a measurable set of
positive measure satisfies the conclusion of Erdős 949. -/
theorem witness_of_measurable_subset_pos (hSF : SumFree S) {S₀ : Set ℝ} (hsub : S₀ ⊆ S)
    (hm : MeasurableSet S₀) (hpos : 0 < volume S₀) : Witness S := by
  obtain ⟨ε, hε, hgap⟩ := gap_of_measurable_subset_pos hSF hsub hm hpos
  exact witness_of_gap hε hgap

/-- Contrapositive shape: a sum-free `S` that is a counterexample to Erdős 949 has inner
Lebesgue measure zero — every measurable subset of it is null. -/
theorem inner_measure_zero_of_no_witness (hSF : SumFree S) (hno : ¬ Witness S) :
    ∀ S₀ ⊆ S, MeasurableSet S₀ → volume S₀ = 0 := by
  intro S₀ hsub hm
  by_contra hne
  exact hno (witness_of_measurable_subset_pos hSF hsub hm (pos_iff_ne_zero.2 hne))

/-- Contrapositive shape: a counterexample must accumulate at the origin. -/
theorem accumulates_at_zero_of_no_witness (hno : ¬ Witness S) :
    ∀ ε > (0 : ℝ), ∃ x ∈ S, x ∈ Ioo (-ε) ε := by
  intro ε hε
  by_contra hcon
  push_neg at hcon
  exact hno (witness_of_gap hε fun x hx hxS => hcon x hxS hx)

end Erdos949Close

/-! ### Axiom receipts -/

#print axioms Erdos949Close.gap_of_measurable_subset_pos
#print axioms Erdos949Close.witness_of_measurable_subset_pos
#print axioms Erdos949Close.inner_measure_zero_of_no_witness
#print axioms Erdos949Close.accumulates_at_zero_of_no_witness
