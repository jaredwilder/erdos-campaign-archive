/-
  EG411 delta-calculus - 2026-08-31, round 3 of the MSL flow session.

  The defect calculus for 3*phi(N) = 2N+2. With d := 3*phi(M) - 2*M (the defect)
  and u := (d+2)/2, all statements kept subtraction-free:

  * exact_quotient      : forward W24 - the top prime satisfies
                          q * 3*phi(M) = 2*M*q + 3*phi(M) + 2
  * defect_pos          : every proper cofactor has positive defect: 2M < 3*phi(M)
  * extension           : backward W24 - THE GENERATIVE THEOREM: a prefix M with
                          3*phi(M) = 2M + 2u and u*q = M+1+u, q prime, q not | M,
                          yields the solution N = M*q
  * defect_recursion    : 3*phi(M*q) + 2M + d = 2*M*q + d*q  (D48, additive form)
  * anchor_product      : u*(M*q+1) = (M+1)*(M+u)  (W29's engine)
  * anchor_law          : u odd => v2(N+1) = v2(M+1) + v2(M+u)  (W29; the Balance
                          Law is the u = 1 fibre)
  * cascade_termination : 17 | 6^8+1, hence 6^8+1 is not prime - the squaring
                          orbit x -> x^2 from x = 6 dies at k = 4  (W33)
  * grid instances      : E_5 members 55, 715, 1435 verified through totient_mul;
                          35 rebuilt from its E_2 tower by the generative theorem
-/
import Mathlib

namespace EG411Delta

open Finset

/-- Forward W24: if N = M*q is a solution with q prime not dividing M,
    the top prime satisfies the exact-quotient identity
    q * (3*phi(M)) = 2*M*q + 3*phi(M) + 2. -/
theorem exact_quotient (M q : ℕ) (hq : q.Prime) (hnd : ¬ q ∣ M)
    (heq : 3 * (M * q).totient = 2 * (M * q) + 2) :
    q * (3 * M.totient) = 2 * M * q + 3 * M.totient + 2 := by
  have hcop : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).mpr hnd
  have htot : (M * q).totient = M.totient * (q - 1) := by
    rw [Nat.totient_mul hcop.symm, Nat.totient_prime hq]
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
  have hk1 : q - 1 = k := by omega
  rw [htot, hk1] at heq
  have h1 : 3 * (M.totient * k) = 3 * M.totient * k := by ring
  have h2 : 2 * (M * q) + 2 = 2 * M * k + 2 * M + 2 := by rw [hk]; ring
  have h3 : q * (3 * M.totient) = 3 * M.totient * k + 3 * M.totient := by rw [hk]; ring
  have h4 : 2 * M * q + 3 * M.totient + 2 = 2 * M * k + 2 * M + 3 * M.totient + 2 := by
    rw [hk]; ring
  omega

/-- Every proper cofactor of a solution has positive defect: 2*M < 3*phi(M). -/
theorem defect_pos (M q : ℕ) (hq : q.Prime) (hnd : ¬ q ∣ M)
    (heq : 3 * (M * q).totient = 2 * (M * q) + 2) : 2 * M < 3 * M.totient := by
  have h := exact_quotient M q hq hnd heq
  by_contra hle
  push_neg at hle
  have h1 : q * (3 * M.totient) ≤ q * (2 * M) := Nat.mul_le_mul_left q hle
  have h2 : q * (2 * M) = 2 * M * q := by ring
  omega

/-- Backward W24 - THE GENERATIVE THEOREM: a prefix M with defect 2u
    (3*phi(M) = 2*M + 2*u) and an admissible new prime q with
    u*q = M + 1 + u (that is, q = 1 + (M+1)/u) produces a solution N = M*q.
    Squarefreeness is not needed for this direction. -/
theorem extension (M q u : ℕ) (hq : q.Prime) (hnd : ¬ q ∣ M)
    (hM : 3 * M.totient = 2 * M + 2 * u) (hu : u * q = M + 1 + u) :
    3 * (M * q).totient = 2 * (M * q) + 2 := by
  have hcop : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).mpr hnd
  have htot : (M * q).totient = M.totient * (q - 1) := by
    rw [Nat.totient_mul hcop.symm, Nat.totient_prime hq]
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
  have hk1 : q - 1 = k := by omega
  have huk : u * k = M + 1 := by
    have hexp : u * q = u * k + u := by rw [hk]; ring
    omega
  have hTk : 3 * (M.totient * k) = 3 * M.totient * k := by ring
  have hMk : 3 * M.totient * k = (2 * M + 2 * u) * k := by rw [hM]
  have hexp2 : (2 * M + 2 * u) * k = 2 * M * k + 2 * (u * k) := by ring
  have hgoal : 2 * (M * q) + 2 = 2 * M * k + 2 * M + 2 := by rw [hk]; ring
  rw [htot, hk1]
  omega

/-- D48, the defect recursion in additive form: if 3*phi(M) = 2*M + d then
    3*phi(M*q) + 2*M + d = 2*M*q + d*q for any new prime q. -/
theorem defect_recursion (M q d : ℕ) (hq : q.Prime) (hnd : ¬ q ∣ M)
    (hM : 3 * M.totient = 2 * M + d) :
    3 * (M * q).totient + 2 * M + d = 2 * M * q + d * q := by
  have hcop : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).mpr hnd
  have htot : (M * q).totient = M.totient * (q - 1) := by
    rw [Nat.totient_mul hcop.symm, Nat.totient_prime hq]
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
  have hk1 : q - 1 = k := by omega
  have hTk : 3 * (M.totient * k) = 3 * M.totient * k := by ring
  have hMk : 3 * M.totient * k = (2 * M + d) * k := by rw [hM]
  have hexp : (2 * M + d) * k = 2 * M * k + d * k := by ring
  have hq2 : 2 * M * q + d * q = 2 * M * k + 2 * M + (d * k + d) := by rw [hk]; ring
  rw [htot, hk1]
  omega

/-- W29's engine, a pure identity: from u*q = M+1+u follows
    u*(M*q+1) = (M+1)*(M+u). -/
theorem anchor_product (M q u : ℕ) (hu : u * q = M + 1 + u) :
    u * (M * q + 1) = (M + 1) * (M + u) := by
  have h1 : u * (M * q + 1) = M * (u * q) + u := by ring
  rw [h1, hu]
  ring

/-- W29, THE ANCHOR LAW: for odd u, the 2-adic depth of N+1 = M*q+1 splits as
    v2(M+1) + v2(M+u). The Balance Law is the u = 1 fibre. -/
theorem anchor_law (M q u : ℕ) (hu : u * q = M + 1 + u) (hodd : Odd u) :
    (M * q + 1).factorization 2 = (M + 1).factorization 2 + (M + u).factorization 2 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rcases hodd with ⟨m, hm⟩
    omega
  have hprod := anchor_product M q u hu
  have hn1 : M * q + 1 ≠ 0 := Nat.succ_ne_zero _
  have hm1 : M + 1 ≠ 0 := Nat.succ_ne_zero _
  have hmu : M + u ≠ 0 := by omega
  have hL : (u * (M * q + 1)).factorization 2
      = u.factorization 2 + (M * q + 1).factorization 2 := by
    rw [Nat.factorization_mul hu0 hn1]
    rfl
  have hR : ((M + 1) * (M + u)).factorization 2
      = (M + 1).factorization 2 + (M + u).factorization 2 := by
    rw [Nat.factorization_mul hm1 hmu]
    rfl
  have hu2 : u.factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    rintro ⟨m, hm⟩
    rcases hodd with ⟨t, ht⟩
    omega
  have hkey : u.factorization 2 + (M * q + 1).factorization 2
      = (M + 1).factorization 2 + (M + u).factorization 2 := by
    rw [← hL, ← hR, hprod]
  omega

/-- W33, CASCADE TERMINATION: 17 divides 6^8 + 1, so the squaring orbit
    x -> x^2 from x = 6 produces no fifth solution: the required new prime
    6^8 + 1 is composite. -/
theorem cascade_termination : ¬ Nat.Prime (6 ^ 8 + 1) := by
  intro h
  have h17 : (17 : ℕ) ∣ 6 ^ 8 + 1 := by norm_num
  rcases (Nat.Prime.eq_one_or_self_of_dvd h 17 h17) with h1 | h1 <;> norm_num at h1

/-- Grid instance: M = 55 lies in E_5 (defect 10). -/
theorem grid_E5_55 : 3 * Nat.totient 55 = 2 * 55 + 2 * 5 := by
  have h : Nat.totient 55 = 40 := by
    rw [show (55 : ℕ) = 5 * 11 by norm_num,
        Nat.totient_mul (by decide : Nat.Coprime 5 11),
        Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]
  rw [h]

/-- Grid instance: M = 715 = 5*11*13 lies in E_5. -/
theorem grid_E5_715 : 3 * Nat.totient 715 = 2 * 715 + 2 * 5 := by
  have h143 : Nat.totient 143 = 120 := by
    rw [show (143 : ℕ) = 11 * 13 by norm_num,
        Nat.totient_mul (by decide : Nat.Coprime 11 13),
        Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]
  have h : Nat.totient 715 = 480 := by
    rw [show (715 : ℕ) = 5 * 143 by norm_num,
        Nat.totient_mul (by decide : Nat.Coprime 5 143),
        Nat.totient_prime (by norm_num), h143]
  rw [h]

/-- Grid instance: M = 1435 = 5*7*41 lies in E_5. -/
theorem grid_E5_1435 : 3 * Nat.totient 1435 = 2 * 1435 + 2 * 5 := by
  have h287 : Nat.totient 287 = 240 := by
    rw [show (287 : ℕ) = 7 * 41 by norm_num,
        Nat.totient_mul (by decide : Nat.Coprime 7 41),
        Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]
  have h : Nat.totient 1435 = 960 := by
    rw [show (1435 : ℕ) = 5 * 287 by norm_num,
        Nat.totient_mul (by decide : Nat.Coprime 5 287),
        Nat.totient_prime (by norm_num), h287]
  rw [h]

/-- The generative theorem in action: the second tower of 35, rebuilt from the
    E_2 prefix M = 7 with u = 2, q = 5. -/
theorem grid_extend_35 : 3 * Nat.totient 35 = 2 * 35 + 2 := by
  have h7 : 3 * Nat.totient 7 = 2 * 7 + 2 * 2 := by
    rw [Nat.totient_prime (by norm_num)]
  have h := extension 7 5 2 (by norm_num) (by decide) h7 (by norm_num)
  simpa using h

end EG411Delta
