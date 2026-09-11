import Mathlib

/-!
Erdős 1061, adversarial-mine promotion (opus ranked auditor, 2026-09-02). Counting
σ(a)+σ(b)=σ(a+b): the useful exact fact the campaign held is that a = b never works,
because σ(2a) > 2σ(a) for every a ≥ 1: the divisors of 2a include 2d for every d ∣ a
(distinct, summing to 2σ(a)) and also 1, which is not of that form since 2a ≥ 2·1.
So every solution has a ≠ b. The asymptotic count itself is untouched here.
-/

set_option autoImplicit false

open ArithmeticFunction

theorem erdos1061_sigma_double (a : ℕ) (ha : 1 ≤ a) : 2 * sigma 1 a < sigma 1 (2 * a) := by
  rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply]
  have h2a : 2 * a ≠ 0 := by omega
  -- the doubled divisors of a sit inside the divisors of 2a
  have hmap : ((a.divisors).image (fun d => 2 * d)) ⊆ (2 * a).divisors := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    have hdvd : d ∣ a := (Nat.mem_divisors.mp hd).1
    exact Nat.mem_divisors.mpr ⟨mul_dvd_mul_left 2 hdvd, h2a⟩
  have hinj : ∀ x ∈ a.divisors, ∀ y ∈ a.divisors, 2 * x = 2 * y → x = y := by
    intro x _ y _ h
    omega
  have hsum : ∑ x ∈ (a.divisors).image (fun d => 2 * d), x = 2 * ∑ d ∈ a.divisors, d := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
  -- 1 divides 2a but is not a doubled divisor
  have hone : (1 : ℕ) ∈ (2 * a).divisors := Nat.one_mem_divisors.mpr h2a
  have hnot : (1 : ℕ) ∉ (a.divisors).image (fun d => 2 * d) := by
    intro h
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp h
    omega
  have hsub : insert 1 ((a.divisors).image (fun d => 2 * d)) ⊆ (2 * a).divisors := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hone
    · exact hmap hx
  calc 2 * ∑ d ∈ a.divisors, d
      < 1 + 2 * ∑ d ∈ a.divisors, d := by omega
    _ = ∑ x ∈ insert 1 ((a.divisors).image (fun d => 2 * d)), x := by
        rw [Finset.sum_insert hnot, hsum]
    _ ≤ ∑ x ∈ (2 * a).divisors, x := Finset.sum_le_sum_of_subset hsub

theorem erdos1061_no_equal_split (a : ℕ) (ha : 1 ≤ a) :
    sigma 1 a + sigma 1 a ≠ sigma 1 (a + a) := by
  have h := erdos1061_sigma_double a ha
  rw [show a + a = 2 * a by ring]
  omega
