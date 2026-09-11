import Mathlib

/-!
Erdős 479, P0 promotion (GPT gold pack rank 2, audited 2026-09-01; kernel round 2026-09-02).
Infinite parametric witness family: for every j ≥ 0 and every odd prime p, with
k = 2^(2^j) and n = 2^j · p, we have 2^n ≡ k (mod n). Modulo p by Fermat
(2^(2^j(p-1)) ≡ 1), modulo 2^j both sides vanish (j ≤ 2^j), and CRT since gcd(2^j, p) = 1.
As p varies this gives infinitely many n for each such k.
-/

set_option autoImplicit false

theorem erdos479_family (j p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    2 ^ (2 ^ j * p) ≡ 2 ^ (2 ^ j) [MOD 2 ^ j * p] := by
  have hcop2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd)
  have hcop : Nat.Coprime (2 ^ j) p := hcop2.pow_left j
  refine (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨?_, ?_⟩
  · have hj : j ≤ 2 ^ j := Nat.lt_two_pow_self.le
    have h1 : 2 ^ j ∣ 2 ^ (2 ^ j * p) :=
      pow_dvd_pow 2 (le_trans hj (Nat.le_mul_of_pos_right _ hp.pos))
    have h2 : 2 ^ j ∣ 2 ^ (2 ^ j) := pow_dvd_pow 2 hj
    exact (Nat.modEq_zero_iff_dvd.mpr h1).trans (Nat.modEq_zero_iff_dvd.mpr h2).symm
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    have hf : 2 ^ q ≡ 1 [MOD q + 1] := by
      have := Nat.ModEq.pow_card_sub_one_eq_one hp hcop2
      simpa using this
    have hpow : (2 ^ q) ^ (2 ^ j) ≡ 1 [MOD q + 1] := by
      simpa using hf.pow (2 ^ j)
    have hmul := hpow.mul_right (2 ^ (2 ^ j))
    rw [one_mul, ← pow_mul, ← pow_add] at hmul
    have hexp : q * 2 ^ j + 2 ^ j = 2 ^ j * (q + 1) := by ring
    rwa [hexp] at hmul
