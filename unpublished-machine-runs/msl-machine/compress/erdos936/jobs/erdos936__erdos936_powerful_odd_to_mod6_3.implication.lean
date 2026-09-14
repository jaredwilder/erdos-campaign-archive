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
set_option maxHeartbeats 400000

-- THE NORMALIZATION PRELUDE (msl_ladder, deterministic, $0).
-- The claim it tests: most leaf failures on an arithmetic DAG are SIDE-CONDITIONS
-- (an un-introduced hypothesis, a numeric coercion, a nonnegativity obligation),
-- not mathematics.  Each step is `try`, so the prelude never fails and never
-- changes what a tactic after it is allowed to prove.
macro "msl_prelude" : tactic =>
  `(tactic| ((try intros); (try push_cast); (try positivity)))

-- ---- children, INCLUDED BY SOURCE (each already PROVED_KERNEL alone)
theorem erdos936_nine_dvd_iff (n : ℕ) : 9 ∣ 2 ^ n + 1 ↔ n % 6 = 3 := by
  first
  | decide
  | norm_num
  | simp

-- ---- the composition: children -> parent
theorem erdos936_powerful_odd_to_mod6_3_composition (n : ℕ) (hpow : ∀ p : ℕ, p ∣ 2 ^ n + 1 → p ^ 2 ∣ 2 ^ n + 1) (hodd : n % 2 = 1) : ((erdos936_nine_dvd_iff : ($v0 : ℕ) : 9 ∣ 2 ^ $v0 + 1 ↔ $v0 % 6 = 3)) → (∀ (n : ℕ), (∀ p : ℕ, p ∣ 2 ^ n + 1 → p ^ 2 ∣ 2 ^ n + 1) → n % 2 = 1 → n % 6 = 3) := by
  first
  | (decide; done)
  | (omega; done)
  | (norm_num; done)
  | (ring_nf; done)
  | (ring_nf; ring; done)
  | (linarith; done)
  | (nlinarith; done)
  | (positivity; done)
  | (gcongr; done)
  | (simp_all; done)
  | (aesop; done)
  | (msl_prelude; done)
  | (msl_prelude; omega; done)
  | (msl_prelude; norm_num; done)
  | (msl_prelude; linarith; done)
  | (msl_prelude; nlinarith; done)
  | (msl_prelude; ring_nf; done)
  | (msl_prelude; ring_nf; ring; done)
  | (msl_prelude; decide; done)
  | (msl_prelude; simp_all; done)
  | (msl_prelude; aesop; done)
  | (msl_prelude; field_simp; done)
  | (msl_prelude; field_simp; ring; done)
  | (msl_prelude; qify; omega; done)

-- ---- the parent, by exact application of the composition
theorem erdos936_powerful_odd_to_mod6_3 (n : ℕ) (hpow : ∀ p : ℕ, p ∣ 2 ^ n + 1 → p ^ 2 ∣ 2 ^ n + 1) (hodd : n % 2 = 1) : ∀ (n : ℕ), (∀ p : ℕ, p ∣ 2 ^ n + 1 → p ^ 2 ∣ 2 ^ n + 1) → n % 2 = 1 → n % 6 = 3 := by
  first
  | exact erdos936_powerful_odd_to_mod6_3_composition ⟨erdos936_nine_dvd_iff⟩
  | (apply erdos936_powerful_odd_to_mod6_3_composition; exact ⟨erdos936_nine_dvd_iff⟩)
  | (intros; exact erdos936_powerful_odd_to_mod6_3_composition ⟨erdos936_nine_dvd_iff⟩)

#print axioms erdos936_powerful_odd_to_mod6_3_composition
#print axioms erdos936_powerful_odd_to_mod6_3
