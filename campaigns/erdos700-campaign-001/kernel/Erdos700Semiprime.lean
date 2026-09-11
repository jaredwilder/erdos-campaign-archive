import Mathlib

/-!
Erdős 700, P0 promotion (GPT gold pack rank 4, audited 2026-09-01; kernel round 2026-09-02).
f(n) = min_{1<k≤n/2} gcd(n, C(n,k)). For primes p < q: every admissible k has
gcd(pq, C(pq,k)) ≥ p (since n / gcd(n, C(n,k)) divides k, a gcd of 1 would force pq ∣ k),
and k = q attains exactly p: p ∣ C(pq, q) by Lucas mod p, while q ∤ C(pq, q) because
q · C(pq, q) = pq · C(pq−1, q−1) and C(pq−1, q−1) ≡ 1 (mod q) by Lucas.
Hence f(pq) = p = min(p, q). (Lower bound for p ≤ q; exact value at k = q for p < q.)
-/

set_option autoImplicit false

theorem erdos700_lower (p q k : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q)
    (hk1 : 1 < k) (hk2 : k ≤ p * q / 2) : p ≤ Nat.gcd (p * q) ((p * q).choose k) := by
  by_contra hlt
  push_neg at hlt
  have hpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  obtain ⟨g1, g2, h1, h2, hg12'⟩ :=
    Nat.dvd_mul.mp (Nat.gcd_dvd_left (p * q) ((p * q).choose k))
  have hg12 : Nat.gcd (p * q) ((p * q).choose k) = g1 * g2 := hg12'.symm
  rcases (Nat.dvd_prime hp).mp h1 with h1 | h1 <;>
    rcases (Nat.dvd_prime hq).mp h2 with h2 | h2 <;> rw [h1, h2] at hg12
  · have hcop : Nat.Coprime (p * q) ((p * q).choose k) := by
      rw [Nat.coprime_iff_gcd_eq_one, hg12, one_mul]
    have hn : p * q ∣ (p * q).choose k * k := by
      obtain ⟨n, hn⟩ : ∃ n, p * q = n + 1 := ⟨p * q - 1, by omega⟩
      obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hid := Nat.succ_mul_choose_eq n j
      simp only [Nat.succ_eq_add_one] at hid
      rw [hn, hj, ← hid]
      exact dvd_mul_right _ _
    have hdk : p * q ∣ k := hcop.dvd_of_dvd_mul_left hn
    have := Nat.le_of_dvd (by omega) hdk
    omega
  · rw [hg12, one_mul] at hlt
    omega
  · rw [hg12, mul_one] at hlt
    omega
  · rw [hg12] at hlt
    have : p ≤ p * q := Nat.le_mul_of_pos_right _ hq.pos
    omega

theorem erdos700_choose_q_gcd (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Nat.gcd (p * q) ((p * q).choose q) = p := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  have hpdvd : p ∣ (p * q).choose q := by
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div (n := p * q) (k := q) (p := p)
    have hmod : p * q % p = 0 := Nat.mul_mod_right p q
    have hqp : q % p ≠ 0 := by
      intro h
      have hdv : p ∣ q := Nat.dvd_of_mod_eq_zero h
      rcases (Nat.dvd_prime hq).mp hdv with h1 | h1
      · exact hp.one_lt.ne' h1
      · omega
    have h0 : Nat.choose (p * q % p) (q % p) = 0 := by
      rw [hmod]
      exact Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hqp)
    rw [h0] at hl
    simp only [Nat.cast_zero, zero_mul] at hl
    exact_mod_cast Int.modEq_zero_iff_dvd.mp hl
  have hqndvd : ¬ q ∣ (p * q).choose q := by
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq.pos; omega⟩
    subst hq'
    have hid := Nat.succ_mul_choose_eq (q' + p' * (q' + 1)) q'
    simp only [Nat.succ_eq_add_one] at hid
    have hN : q' + p' * (q' + 1) + 1 = p * (q' + 1) := by rw [hp']; ring
    rw [hN] at hid
    -- hid : p * (q'+1) * choose (q'+p'*(q'+1)) q' = choose (p*(q'+1)) (q'+1) * (q'+1)
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div
      (n := q' + p' * (q' + 1)) (k := q') (p := q' + 1)
    have hm1 : (q' + p' * (q' + 1)) % (q' + 1) = q' := by
      rw [Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    have hd1 : (q' + p' * (q' + 1)) / (q' + 1) = p' := by
      rw [Nat.add_mul_div_right _ _ (by omega : 0 < q' + 1)]
      rw [Nat.div_eq_of_lt (by omega), zero_add]
    have hm2 : q' % (q' + 1) = q' := Nat.mod_eq_of_lt (by omega)
    have hd2 : q' / (q' + 1) = 0 := Nat.div_eq_of_lt (by omega)
    rw [hm1, hd1, hm2, hd2, Nat.choose_self, Nat.choose_zero_right] at hl
    simp only [Nat.cast_one, one_mul] at hl
    -- hl : ↑(choose (q'+p'*(q'+1)) q') ≡ 1 [ZMOD (q'+1)]
    have hnot : ¬ (q' + 1) ∣ (q' + p' * (q' + 1)).choose q' := by
      intro hdv
      have h0 : ((q' + p' * (q' + 1)).choose q' : ℤ) ≡ 0 [ZMOD ((q' + 1 : ℕ) : ℤ)] :=
        Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr hdv)
      have h10 : (1 : ℤ) ≡ 0 [ZMOD ((q' + 1 : ℕ) : ℤ)] := hl.symm.trans h0
      have hdq : (((q' + 1 : ℕ)) : ℤ) ∣ 1 := Int.modEq_zero_iff_dvd.mp h10
      have hq1 : (q' + 1) ∣ 1 := by exact_mod_cast hdq
      exact hq.one_lt.ne' (Nat.dvd_one.mp hq1)
    have hcancel : p * (q' + p' * (q' + 1)).choose q' = (p * (q' + 1)).choose (q' + 1) := by
      apply Nat.eq_of_mul_eq_mul_right (show 0 < q' + 1 by omega)
      rw [← hid]
      ring
    intro hdv
    rw [← hcancel] at hdv
    rcases (Nat.Prime.dvd_mul hq).mp hdv with h | h
    · rcases (Nat.dvd_prime hp).mp h with h1 | h1
      · exact hq.one_lt.ne' h1
      · omega
    · exact hnot h
  have hgdvd := Nat.gcd_dvd_left (p * q) ((p * q).choose q)
  have hgC := Nat.gcd_dvd_right (p * q) ((p * q).choose q)
  have hpg : p ∣ Nat.gcd (p * q) ((p * q).choose q) := Nat.dvd_gcd (dvd_mul_right p q) hpdvd
  obtain ⟨g1, g2, h1, h2, hg12'⟩ := Nat.dvd_mul.mp hgdvd
  have hg12 : Nat.gcd (p * q) ((p * q).choose q) = g1 * g2 := hg12'.symm
  rcases (Nat.dvd_prime hp).mp h1 with h1 | h1 <;>
    rcases (Nat.dvd_prime hq).mp h2 with h2 | h2 <;> rw [h1, h2] at hg12
  · rw [hg12, one_mul] at hpg
    exact absurd (Nat.dvd_one.mp hpg) hp.one_lt.ne'
  · exfalso
    apply hqndvd
    rw [hg12, one_mul] at hgC
    exact hgC
  · rw [hg12, mul_one]
  · exfalso
    apply hqndvd
    rw [hg12] at hgC
    exact dvd_trans (dvd_mul_left q p) hgC