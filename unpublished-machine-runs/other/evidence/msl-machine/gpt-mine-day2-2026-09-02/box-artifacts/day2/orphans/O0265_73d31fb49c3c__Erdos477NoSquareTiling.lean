import Mathlib

set_option autoImplicit false


/-!
Erdős 477, P0 promotion (GPT gold pack rank 3, audited 2026-09-01; kernel round 2026-09-02).
Natural slice f(k) = k²: there is no A ⊆ ℤ such that every integer is uniquely a + k².
B - B for B = {k²} is exactly {m : m ≢ 2 mod 4}; uniqueness forces every nonzero difference
inside A to be ≡ 2 mod 4, so |A| ≤ 2; a finite A plus nonnegative squares is bounded below.
-/


theorem erdos477_sq_sub_sq_of_mod_four (m : ℤ) (h : m % 4 ≠ 2) : ∃ k l : ℤ, m = k ^ 2 - l ^ 2 := by
  rcases Int.emod_two_eq_zero_or_one m with h2 | h2
  · obtain ⟨t, rfl⟩ : ∃ t, m = 4 * t := ⟨m / 4, by omega⟩
    exact ⟨t + 1, t - 1, by ring⟩
  · obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
    exact ⟨t + 1, t, by ring⟩

theorem erdos477_no_square_tiling :
    ¬ ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ (∃ k : ℤ, p.2 = k ^ 2) ∧ n = p.1 + p.2 := by
  rintro ⟨A, hA⟩
  have hdiff : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → (a - a') % 4 = 2 := by
    intro a ha a' ha' hne
    by_contra hmod
    obtain ⟨k, l, hkl⟩ := erdos477_sq_sub_sq_of_mod_four (a - a') hmod
    obtain ⟨p, _, huniq⟩ := hA (a + l ^ 2)
    have h1 : (a, l ^ 2) = p := huniq (a, l ^ 2) ⟨ha, ⟨l, rfl⟩, rfl⟩
    have h2 : (a', k ^ 2) = p := huniq (a', k ^ 2) ⟨ha', ⟨k, rfl⟩, by linarith⟩
    have h3 := congrArg Prod.fst (h1.trans h2.symm)
    simp at h3
    exact hne h3
  obtain ⟨p0, ⟨ha0, _, _⟩, _⟩ := hA 0
  have ha0' : p0.1 ∈ A := ha0
  by_cases hsingle : ∀ a ∈ A, a = p0.1
  · obtain ⟨p, ⟨hp1, ⟨k, hk⟩, hn⟩, _⟩ := hA (p0.1 - 1)
    have hp := hsingle p.1 hp1
    linarith [sq_nonneg k]
  · push_neg at hsingle
    obtain ⟨a1, ha1, hne⟩ := hsingle
    have htwo : ∀ a ∈ A, a = p0.1 ∨ a = a1 := by
      intro a ha
      by_contra hcon
      push_neg at hcon
      have h01 := hdiff p0.1 ha0' a1 ha1 (Ne.symm hne)
      have h0a := hdiff a ha p0.1 ha0' hcon.1
      have h1a := hdiff a ha a1 ha1 hcon.2
      omega
    obtain ⟨p, ⟨hp1, ⟨k, hk⟩, hn⟩, _⟩ := hA (min p0.1 a1 - 1)
    rcases htwo p.1 hp1 with h | h
    · have := min_le_left p0.1 a1
      linarith [sq_nonneg k]
    · have := min_le_right p0.1 a1
      linarith [sq_nonneg k]

-- axiom footprint
#print axioms erdos477_sq_sub_sq_of_mod_four
#print axioms erdos477_no_square_tiling
