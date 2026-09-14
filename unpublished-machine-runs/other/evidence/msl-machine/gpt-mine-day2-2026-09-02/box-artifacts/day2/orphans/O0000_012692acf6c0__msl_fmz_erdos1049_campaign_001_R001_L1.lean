import Mathlib

set_option autoImplicit false


namespace Erdos1049L1Close
open ArithmeticFunction Filter

lemma lambert_convergent_core (t : ℝ) (ht : 1 < |t|) :
    ∑' n : ℕ+, 1 / (t ^ (n : ℕ) - 1) =
    ∑' n : ℕ+, ((n : ℕ).divisors.card : ℝ) / (t ^ (n : ℕ)) := by
  have ht0 : t ≠ 0 := fun h => by subst h; simp at ht; linarith [abs_nonneg (0:ℝ)]
  have htn : ∀ n : ℕ, t ^ n ≠ 0 := fun n => pow_ne_zero n ht0
  set r : ℝ := t⁻¹ with hr_def
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, hr_def, abs_inv]; exact inv_lt_one_of_one_lt₀ ht
  have h := tsum_pow_div_one_sub_eq_tsum_sigma (k := 0) hr_norm
  convert h using 1
  · apply tsum_congr; intro n
    have hp : t ^ (n : ℕ) ≠ 0 := htn n
    have hrn : r ^ (n : ℕ) = (t ^ (n : ℕ))⁻¹ := by rw [hr_def, inv_pow]
    have hne1 : t ^ (n : ℕ) - 1 ≠ 0 := by
      intro hc
      have ht1 : t ^ (n : ℕ) = 1 := by linarith [sub_eq_zero.mp hc]
      have habs1 : |t| ^ (n : ℕ) = 1 := by rw [← abs_pow, ht1]; simp
      have hlt : 1 < |t| ^ (n : ℕ) := one_lt_pow₀ ht n.pos.ne'
      linarith
    rw [hrn]; field_simp
  · apply tsum_congr; intro n
    have hp : t ^ (n : ℕ) ≠ 0 := htn n
    have hrn : r ^ (n : ℕ) = (t ^ (n : ℕ))⁻¹ := by rw [hr_def, inv_pow]
    rw [hrn, ArithmeticFunction.sigma_zero_apply]; field_simp

end Erdos1049L1Close

theorem msl_fmz_erdos1049_campaign_001_R001_L1  : namespace Erdos1049L1Close
open ArithmeticFunction Filter

/-- LEMMA L1, full scope: for every rational t > 1, the Lambert τ-identity
    Σ 1/(t^n − 1) = Σ τ(n)/t^n holds exactly, in the frozen problem's encoding. -/
theorem erdos1049_L1_full (t : ℚ) (ht : 1 < t) :
    ∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)
      = ∑' n : ℕ+, ((n : ℕ).divisors.card : ℝ) / (t : ℝ) ^ (n : ℕ) := by
  have hpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have habs : |(t : ℝ)| = (t : ℝ) := abs_of_pos hpos
  exact Erdos1049L1Close.lambert_convergent_core (t : ℝ) (by rw [habs]; exact_mod_cast ht)

end Erdos1049L1Close := by
  have hpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have habs : |(t : ℝ)| = (t : ℝ) := abs_of_pos hpos
  exact Erdos1049L1Close.lambert_convergent_core (t : ℝ) (by rw [habs]; exact_mod_cast ht)

-- axiom footprint
#print axioms Erdos1049L1Close.lambert_convergent_core
#print axioms msl_fmz_erdos1049_campaign_001_R001_L1
#print axioms erdos1049_L1_full
