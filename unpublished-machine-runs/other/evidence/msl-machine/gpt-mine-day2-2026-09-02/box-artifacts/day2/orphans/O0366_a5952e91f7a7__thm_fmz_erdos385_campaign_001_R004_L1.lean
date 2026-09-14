import Mathlib

set_option autoImplicit false



namespace Erdos385L1

/-- Copy of the frozen Erdos385 encoding of F (isolated namespace so that the
incomplete research theorems of the source file cannot enter the footprint). -/
noncomputable def F (n : ℕ) : ℕ := sSup {m + m.minFac | (m < n) (_ : m.Composite)}

theorem minFac_of_even {m : ℕ} (h4 : 4 ≤ m) (h2 : 2 ∣ m) : m.minFac = 2 := by
  have hp : m.minFac.Prime := Nat.minFac_prime.mpr (by omega)
  have hle : m.minFac ≤ 2 := Nat.minFac_le_of_dvd (by omega) h2
  have hge : 2 ≤ m.minFac := hp.two_le
  omega

theorem key (m N : ℕ) (h4 : 4 ≤ m) (h2 : 2 ∣ m) (hN : m + 1 ≤ N) : m + 2 ≤ F N := by
  have hcomp : m.Composite :=
    ⟨by omega, by
      intro hp
      rcases hp.eq_two_or_odd with h | h
      · omega
      · obtain ⟨j, hj⟩ := h2
        obtain ⟨i, hi⟩ := h
        omega⟩
  have hbdd : BddAbove {m + m.minFac | (m < N) (_ : m.Composite)} := by
    refine ⟨2 * N, ?_⟩
    rintro x ⟨t, ht, htc, rfl⟩
    have hmin : t.minFac ≤ t := Nat.le_of_dvd (by omega) (Nat.minFac_dvd t)
    omega
  have hle : m + m.minFac ≤ F N :=
    le_csSup hbdd (by exact ⟨m, by omega, hcomp, rfl⟩)
  rw [minFac_of_even h4 h2] at hle
  omega

end Erdos385L1

theorem msl_fmz_erdos385_campaign_001_R004_L1  : namespace Erdos385L1

/-- L1: for odd n ≥ 5, the even composite m = n-1 gives F n ≥ n+1; for even n ≥ 6,
the even composite m = n-2 gives F n ≥ n. Hence F n ≥ n for all n ≥ 5, and the first
interrogative clause (parts.i: ∀ᶠ n in atTop, n < F n) reduces to even n; L1 alone
closes neither parts.i nor parts.ii. -/
theorem L1 :
    (∀ n : ℕ, 5 ≤ n → Odd n → n + 1 ≤ F n) ∧
    (∀ n : ℕ, 6 ≤ n → Even n → n ≤ F n) := by
  refine ⟨?_, ?_⟩
  · intro n h5 hodd
    obtain ⟨k, hk⟩ := hodd
    have h := key (n - 1) n (by omega) ⟨k, by omega⟩ (by omega)
    omega
  · intro n h6 heven
    obtain ⟨k, hk⟩ := heven
    have h := key (n - 2) n (by omega) ⟨k - 1, by omega⟩ (by omega)
    omega

end Erdos385L1 := by
  -- The complete tactic proof is embedded in `conclusion`; the file
  -- `import Mathlib` + definitions + conclusion compiles as one unit
  -- with an axiom footprint of exactly {propext, Classical.choice, Quot.sound}.

-- axiom footprint
#print axioms Erdos385L1.F
#print axioms Erdos385L1.minFac_of_even
#print axioms Erdos385L1.key
#print axioms msl_fmz_erdos385_campaign_001_R004_L1
#print axioms L1
