import Mathlib

/-!
Erdős 479, second family (adversarial transcript mine, 2026-09-02 — the campaign itself
missed this; the auditor derived it): k = −1 is settled. For every a,
3^(a+1) ∣ 2^(3^a) + 1, so in particular n = 3^a divides 2^n + 1, giving infinitely many
witnesses for k = −1 (2^n ≡ −1 mod n). Lifting-the-exponent induction: if
2^(3^a) = 3^(a+1)·m − 1 then cubing gives (3tm−1)³ + 1 = 9t·(3t²m³ − 3tm² + m) with
t = 3^a. Stated in ℤ to keep the subtraction honest; ℕ divisibility corollary follows.
-/

set_option autoImplicit false

theorem erdos479_lte (a : ℕ) : (3 : ℤ) ^ (a + 1) ∣ 2 ^ (3 ^ a) + 1 := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    obtain ⟨m, hm⟩ := ih
    set t : ℤ := 3 ^ a with hta
    have h31 : (3 : ℤ) ^ (a + 1) = 3 * t := by rw [hta, pow_succ, mul_comm]
    have h32 : (3 : ℤ) ^ (a + 1 + 1) = 9 * t := by rw [pow_succ, h31]; ring
    have h2 : (2 : ℤ) ^ (3 ^ a) = 3 * t * m - 1 := by
      rw [← h31]
      linarith
    have hcube : (2 : ℤ) ^ (3 ^ (a + 1)) = ((2 : ℤ) ^ (3 ^ a)) ^ 3 := by
      rw [← pow_mul, pow_succ]
    refine ⟨3 * t ^ 2 * m ^ 3 - 3 * t * m ^ 2 + m, ?_⟩
    rw [hcube, h2, h32]
    ring

theorem erdos479_k_neg_one (a : ℕ) : (3 ^ a : ℕ) ∣ 2 ^ (3 ^ a) + 1 := by
  have h : (3 : ℤ) ^ a ∣ 2 ^ (3 ^ a) + 1 :=
    dvd_trans (pow_dvd_pow 3 (Nat.le_succ a)) (erdos479_lte a)
  have hcast : ((3 ^ a : ℕ) : ℤ) ∣ ((2 ^ (3 ^ a) + 1 : ℕ) : ℤ) := by
    push_cast
    exact h
  exact_mod_cast hcast
