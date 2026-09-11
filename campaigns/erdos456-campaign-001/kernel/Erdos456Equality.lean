import Mathlib

/-!
Erdős 456, P0 promotion (GPT gold pack rank 5, audited 2026-09-01; kernel round 2026-09-02).
For every odd prime p and n = p - 1: m_n = p (p - 1 divides φ(p), and no 1 ≤ m < p has
p - 1 ∣ φ(m)), and p_n = p (p ≡ 1 mod p - 1, and no smaller prime is ≡ 1 mod p - 1).
The minima are stated as "witness + nothing smaller", which is exactly what m_n and p_n mean.
-/

set_option autoImplicit false

theorem erdos456_m_eq_p (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (p - 1) ∣ Nat.totient p ∧ ∀ m, 1 ≤ m → m < p → ¬ (p - 1) ∣ Nat.totient m := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  refine ⟨by rw [Nat.totient_prime hp], ?_⟩
  intro m hm1 hmp hdvd
  have hpos : 0 < Nat.totient m := Nat.totient_pos.mpr hm1
  have hle : Nat.totient m ≤ m := Nat.totient_le m
  have hge : p - 1 ≤ Nat.totient m := Nat.le_of_dvd hpos hdvd
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · have := Nat.totient_lt m h1
    omega
  · have hm : m = 1 := by omega
    subst hm
    simp at hge
    omega

theorem erdos456_p_eq_p (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    p ≡ 1 [MOD p - 1] ∧ ∀ q, q.Prime → q < p → ¬ q ≡ 1 [MOD p - 1] := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  refine ⟨((Nat.modEq_iff_dvd' hp.one_le).mpr (dvd_refl _)).symm, ?_⟩
  intro q hq hqp hmod
  have h1 : (p - 1) ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_le).mp hmod.symm
  have hq2 := hq.two_le
  have := Nat.le_of_dvd (by omega) h1
  omega
