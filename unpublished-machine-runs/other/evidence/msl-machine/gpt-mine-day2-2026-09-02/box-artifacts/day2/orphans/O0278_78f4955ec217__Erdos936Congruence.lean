import Mathlib

set_option autoImplicit false


/-!
Erdős 936, adversarial-mine promotion (opus ranked auditor + gold pack, 2026-09-02).
The exact mod-9 periodicity tool for the powerful-number question on 2^n + 1:
9 ∣ 2^n + 1 iff n ≡ 3 (mod 6). Order of 2 mod 9 is 6; the six residues are decided
by the kernel and the periodicity transfers by 2^(n+6) ≡ 2^n (mod 9).
-/


theorem erdos936_period (n : ℕ) : (2 ^ (n + 6) + 1) % 9 = (2 ^ n + 1) % 9 := by
  have h : 2 ^ (n + 6) % 9 = 2 ^ n % 9 := by
    rw [pow_add]
    calc (2 ^ n * 2 ^ 6) % 9 = (2 ^ n % 9) * (2 ^ 6 % 9) % 9 := Nat.mul_mod _ _ _
      _ = (2 ^ n % 9) * 1 % 9 := by norm_num
      _ = 2 ^ n % 9 := by rw [mul_one]; omega
  omega

theorem erdos936_nine_dvd_iff (n : ℕ) : 9 ∣ 2 ^ n + 1 ↔ n % 6 = 3 := by
  have hkey : (2 ^ n + 1) % 9 = (2 ^ (n % 6) + 1) % 9 := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n 6 with h | h
      · rw [Nat.mod_eq_of_lt h]
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
        rw [erdos936_period k, ih k (by omega), Nat.add_mod_right]
  have hlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hcase : ∀ m : ℕ, m < 6 → ((2 ^ m + 1) % 9 = 0 ↔ m = 3) := by decide
  have h := hcase (n % 6) hlt
  omega

-- axiom footprint
#print axioms erdos936_period
#print axioms erdos936_nine_dvd_iff
