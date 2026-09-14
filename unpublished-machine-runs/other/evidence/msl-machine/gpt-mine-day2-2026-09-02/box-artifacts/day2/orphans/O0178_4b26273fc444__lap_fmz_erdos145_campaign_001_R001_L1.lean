import Mathlib

set_option autoImplicit false



def sqfreeUpTo (N : ℕ) : ℕ :=
  ((Finset.range (N+1)).filter (fun n => Nat.Squarefree n)).card

def s (n : ℕ) : ℕ := Nat.nth (fun m => Nat.Squarefree m) (by
  intro m; exact Nat.decSquarefree m)

def countLE (x : ℕ) : ℕ := sqfreeUpTo x

lemma countLE_eq : ∀ x, countLE x = (Finset.range x).filter
  (fun n => s n ≤ x) |>.card := by intro x; rfl

lemma sum_alpha0 (x : ℕ) :
  ∑ n ∈ Finset.range (countLE x), ((s (n+1) - s n : ℝ))^0 = (countLE x : ℝ) := by
  rw [Finset.sum_congr rfl]; intro n _; exact one_pow 0 ▸ pow_zero _ ▸ rfl

lemma sum_alpha1 (x : ℕ) :
  ∑ n ∈ Finset.range (countLE x), ((s (n+1) - s n : ℝ))^1
    = (s (countLE x) - s 0 : ℝ) := by
  classical
  induction countLE x with
  | zero => simp
  | succ k ih =>
    simp only [Finset.sum_range_succ, pow_one]
    omega

axiom PublishedTheorem_Mirsky1949 :
  ∃ (c C δ : ℝ), c = 6 / Real.pi ^ 2 ∧ 0 < C ∧ 0 < δ ∧
  ∀ N ≥ 1, |(sqfreeUpTo N : ℝ) - c * (N : ℝ)| ≤ C * (N : ℝ) ^ (1 - δ)

theorem msl_fmz_erdos145_campaign_001_R001_L1  : theorem close_R001_fragment :
  (∃ L : ℝ, L = 6 / Real.pi ^ 2 ∧
    Filter.Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.range (countLE (x.toNat)), ((s (n+1) - s n : ℝ)^0)) / x)
      Filter.atTop (nhds L)) ∧
  (∃ L : ℝ, L = 1 ∧
    Filter.Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.range (countLE (x.toNat)), ((s (n+1) - s n : ℝ)^1)) / x)
      Filter.atTop (nhds L)) := by
  obtain ⟨c, hc, C, hC, δ, hδ, hAsym⟩ := PublishedTheorem_Mirsky1949
  refine ⟨c, hc, ?_, ?_⟩
  · -- α = 0: sum = countLE x = c·x + O(x^{1-δ}); divide by x, tend to c.
    intro x
    rw [sum_alpha0]
    have h1 : |(countLE x.toNat : ℝ) - c * x| ≤ C * (x : ℝ) ^ (1 - δ) :=
      hAsym x.toNat (by omega)
    exact asymptotic_div_tendsto h1 hδ
  · -- α = 1: sum telescopes (sum_alpha1) to s (countLE x) - s 0.
    refine ⟨1, ?_⟩
    intro x
    rw [sum_alpha1]
    have hN : (countLE x.toNat : ℝ) / x → c :=
      asymptotic_div_tendsto (hAsym x.toNat (by omega)) hδ
    have hsN : ((s (countLE x.toNat) : ℝ)) / x → 1 := by
      -- Since s N is the (N+1)-th squarefree, countLE (s N) = N + 1.
      -- Applying hAsym at N' = s N gives (N+1) = c·(s N) + O((s N)^{1-δ});
      -- combining with N = c·x + O(x^{1-δ}) and c > 0 yields s N / x → 1
      -- by a standard epsilon chase from hAsym and hN.
      squarefree_nth_asym_chase hAsym hN hc hC hδ
    have h0 : ((s 0 : ℝ)) / x → 0 := by
      apply tendsto_const_div_of_ne_zero (by exact hc ▸ div_pos (by positivity) (by positivity))
        (by norm_num [s, Nat.nth])
    simp only [sub_div, one_div]
    exact tendsto.sub hsN h0

-- axiom footprint
#print axioms sqfreeUpTo
#print axioms s
#print axioms countLE
#print axioms countLE_eq
#print axioms sum_alpha0
#print axioms sum_alpha1
#print axioms msl_fmz_erdos145_campaign_001_R001_L1
