import Mathlib

/-!
Erdős 885, P0 promotion (GPT gold pack rank 1, audited 2026-09-01; kernel round 2026-09-02).
Factor-difference / square duality: for N ≥ 1, d ∈ D(N) = {|a-b| : ab = N} iff d² + 4N is a
perfect square. Encoded in ℕ with the ordered pair b ≤ a and a - b = d (that is |a-b| = d).
Forward: (a+b)² = (a-b)² + 4ab. Reverse: s² - d² = (s+d)(s-d) = 4N forces s ≡ d (mod 2),
and a = (s+d)/2, b = (s-d)/2 factor N with a - b = d.
-/

set_option autoImplicit false

theorem erdos885_factor_difference_square (N d : ℕ) (hN : 1 ≤ N) :
    (∃ a b : ℕ, a * b = N ∧ b ≤ a ∧ a - b = d) ↔ ∃ s : ℕ, s * s = d * d + 4 * N := by
  constructor
  · rintro ⟨a, b, hab, hle, hd⟩
    obtain ⟨t, rfl⟩ : ∃ t, a = b + t := ⟨a - b, by omega⟩
    have ht : t = d := by omega
    subst ht
    subst hab
    exact ⟨b + t + b, by ring⟩
  · rintro ⟨s, hs⟩
    have hsd : d ≤ s := by
      by_contra h
      push_neg at h
      have := Nat.mul_self_lt_mul_self h
      omega
    have hsub : s * s - d * d = 4 * N := by omega
    have hprod : (s + d) * (s - d) = 4 * N := by
      rw [← hsub, Nat.mul_self_sub_mul_self_eq]
    rcases Nat.even_or_odd (s + d) with ⟨a, ha⟩ | ⟨a, ha⟩
    · have had : d ≤ a := by omega
      obtain ⟨b, hb⟩ : ∃ b, a = b + d := ⟨a - d, by omega⟩
      have hsd' : s - d = b + b := by omega
      rw [ha, hsd'] at hprod
      have hab : a * b = N := by nlinarith [hprod]
      exact ⟨a, b, hab, by omega, by omega⟩
    · have had : d ≤ a := by omega
      have hsd' : s - d = 2 * (a - d) + 1 := by omega
      rw [ha, hsd'] at hprod
      ring_nf at hprod
      omega
