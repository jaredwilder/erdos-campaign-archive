import Mathlib

set_option autoImplicit false



noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime.decide n
noncomputable def d (n : ℕ) : ℕ := p (n+1) - p n

/-- Sum of squared consecutive-prime gaps over all primes p_n ≤ x.
    Every n with p_n ≤ x satisfies n < p_n ≤ x, so the filter over
    range (x.toNat + 2) captures exactly the terms of the Heath-Brown sum. -/
noncomputable def GapSqSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.filter (fun n => (p n : ℝ) ≤ x) (Finset.range (x.toNat + 2)),
    ((d n : ℕ) : ℝ) ^ 2

/-- Partial sum ∑_{n<N} d_n², the left side of the canonical statement. -/
noncomputable def PartialGapSq (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ((d n : ℕ) : ℝ) ^ 2

theorem p_ge_succ : ∀ n : ℕ, p n ≥ n + 2 := by
  intro n
  induction n with
  | zero => simpa [p] using Nat.le_of_lt (by
      have := Nat.Prime.two_gt_one; simpa using Nat.nth_nat_lt (Nat.Prime.decide 2) (by decide))
  | succ n ih =>
      have hmono : p n < p (n+1) := Nat.nth_strictMono Nat.Prime.nth_strictMono n (n+1) (by omega)
      omega

theorem p_ge_two : ∀ n : ℕ, p n ≥ 2 := fun n => by have := p_ge_succ n; omega

theorem bridge (N : ℕ) (hN : 2 ≤ N) :
    PartialGapSq N ≤ GapSqSum ((p N : ℕ) : ℝ) := by
  unfold PartialGapSq GapSqSum
  refine Finset.sum_le_sum_of_subset ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  constructor
  · exact hn
  · -- cast inequality: (p n : ℝ) ≤ (p N : ℝ), from n < N
    have hlt : n < N := hn
    have hmono : p n ≤ p N := Nat.nth_mono (f := Nat.Prime.decide) (by exact Nat.Prime.nth_strictMono) (Nat.le_of_lt hlt)
    exact_mod_cast hmono

axiom HeathBrown1982_GapMomentBound :
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → GapSqSum x ≤ C * x * Real.log x

theorem msl_fmz_erdos233_campaign_001_R004_L1  : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → PartialGapSq N ≤ C * (p N : ℝ) * Real.log (p N : ℝ) := obtain ⟨C, hC, hb⟩ := HeathBrown1982_GapMomentBound
refine ⟨C, hC, fun N hN => ?_⟩
have hbridge : PartialGapSq N ≤ GapSqSum ((p N : ℕ) : ℝ) := bridge N hN
have hx : 2 ≤ ((p N : ℕ) : ℝ) := by
  exact_mod_cast p_ge_two N
exact hbridge.trans (hb ((p N : ℕ) : ℝ) hx)

-- axiom footprint
#print axioms p
#print axioms d
#print axioms GapSqSum
#print axioms PartialGapSq
#print axioms p_ge_succ
#print axioms p_ge_two
#print axioms bridge
#print axioms msl_fmz_erdos233_campaign_001_R004_L1
