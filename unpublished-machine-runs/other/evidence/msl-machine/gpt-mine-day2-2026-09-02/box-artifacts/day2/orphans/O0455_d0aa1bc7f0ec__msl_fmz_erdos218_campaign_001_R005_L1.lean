import Mathlib

set_option autoImplicit false



open Filter

namespace Erdos218L1

/-- The explicit sequence d_n = (1,2,1,2,...). -/
def d (n : ℕ) : ℕ := if n % 2 = 0 then 1 else 2

def cntLE (N : ℕ) : ℕ := ((Finset.range N).filter (fun n => d (n+1) ≤ d n)).card

def cntGE (N : ℕ) : ℕ := ((Finset.range N).filter (fun n => d n ≤ d (n+1))).card

lemma d_val (n : ℕ) : d (2*n) = 1 ∧ d (2*n+1) = 2 := by
  have h0 : (2*n) % 2 = 0 := by omega
  have h1 : (2*n+1) % 2 = 1 := by omega
  simp [d, h0, h1]

lemma le_cond (n : ℕ) : d (n+1) ≤ d n ↔ n % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [d, h, show (n+1) % 2 = 1 by omega]
  · simp [d, h, show (n+1) % 2 = 0 by omega]

lemma ge_cond (n : ℕ) : d n ≤ d (n+1) ↔ n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [d, h, show (n+1) % 2 = 1 by omega]
  · simp [d, h, show (n+1) % 2 = 0 by omega]

lemma eq_cond (n : ℕ) : d (n+1) = d n ↔ False := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [d, h, show (n+1) % 2 = 1 by omega]
  · simp [d, h, show (n+1) % 2 = 0 by omega]

lemma cntLE_succ (N : ℕ) : cntLE (N+1) = cntLE N + (if N % 2 = 1 then 1 else 0) := by
  unfold cntLE
  rw [Finset.range_succ, Finset.filter_insert]
  by_cases h : d (N+1) ≤ d N
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp),
      if_pos ((le_cond N).mp h)]
  · rw [if_neg h, if_neg (fun hc => h (le_cond N ▸ hc))]

lemma cntLE_eq (N : ℕ) : cntLE N = N / 2 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [cntLE_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one N with h | h <;> simp [h] <;> omega

lemma cntGE_succ (N : ℕ) : cntGE (N+1) = cntGE N + (if N % 2 = 0 then 1 else 0) := by
  unfold cntGE
  rw [Finset.range_succ, Finset.filter_insert]
  by_cases h : d N ≤ d (N+1)
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp),
      if_pos ((ge_cond N).mp h)]
  · rw [if_neg h, if_neg (fun hc => h (ge_cond N ▸ hc))]

lemma cntGE_eq (N : ℕ) : cntGE N = (N + 1) / 2 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [cntGE_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one N with h | h <;> simp [h] <;> omega

lemma ratioLE (N : ℕ) (hN : N ≠ 0) :
    (cntLE N : ℝ) / N = 1/2 - ((N % 2 : ℕ) : ℝ) / (2 * N) := by
  rw [cntLE_eq]
  have hN2 : ((N / 2 : ℕ) : ℝ) * 2 + ((N % 2 : ℕ) : ℝ) = (N : ℝ) :=
    by exact_mod_cast Nat.div_add_mod N 2
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  field_simp [hN2]

lemma ratioGE (N : ℕ) (hN : N ≠ 0) :
    (cntGE N : ℝ) / N = 1/2 + ((N % 2 : ℕ) : ℝ) / (2 * N) := by
  rw [cntGE_eq]
  have hN2 : ((N / 2 : ℕ) : ℝ) * 2 + ((N % 2 : ℕ) : ℝ) = (N : ℝ) :=
    by exact_mod_cast Nat.div_add_mod N 2
  have hN3 : (((N + 1) / 2 : ℕ) : ℝ) = ((N / 2 : ℕ) : ℝ) + ((N % 2 : ℕ) : ℝ) :=
    by have h := (by omega : ((N + 1) / 2 : ℕ) = (N / 2 : ℕ) + (N % 2 : ℕ)); exact_mod_cast h
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  field_simp [hN2, hN3]

lemma key : Filter.Tendsto (fun N : ℕ => ((N % 2 : ℕ) : ℝ) / (2 * N)) Filter.atTop
    (nhds (0 : ℝ)) := by
  refine squeeze_zero ?_ ?_
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · apply Filter.eventually_of_forall
    intro N
    have hr : (N % 2 : ℕ) ≤ 1 := by omega
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h0
      have hr0 : (0 : ℝ) ≤ ((N % 2 : ℕ) : ℝ) := Nat.cast_nonneg'
      have hr1 : ((N % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hr
      rw [abs_div, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * N)]
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith

theorem densityLE : Filter.Tendsto (fun N => (cntLE N : ℝ) / N) Filter.atTop (nhds (1/2)) := by
  have h1 : Filter.Tendsto (fun N : ℕ => (1:ℝ)/2 - ((N % 2 : ℕ):ℝ)/(2*N))
      Filter.atTop (nhds (1/2)) := Filter.Tendsto.sub tendsto_const_nhds key
  refine Filter.Tendsto.congr' ?_ h1
  filter_upwards (Ici_mem_atTop 1) with N hN
  rw [ratioLE N (by omega)]

theorem densityGE : Filter.Tendsto (fun N => (cntGE N : ℝ) / N) Filter.atTop (nhds (1/2)) := by
  have h1 : Filter.Tendsto (fun N : ℕ => (1:ℝ)/2 + ((N % 2 : ℕ):ℝ)/(2*N))
      Filter.atTop (nhds (1/2)) := Filter.Tendsto.add tendsto_const_nhds key
  refine Filter.Tendsto.congr' ?_ h1
  filter_upwards (Ici_mem_atTop 1) with N hN
  rw [ratioGE N (by omega)]

end Erdos218L1

theorem msl_fmz_erdos218_campaign_001_R005_L1  : theorem Erdos218L1.L1 :
    Filter.Tendsto (fun N => (Erdos218L1.cntLE N : ℝ) / N) Filter.atTop (nhds (1/2)) ∧
    Filter.Tendsto (fun N => (Erdos218L1.cntGE N : ℝ) / N) Filter.atTop (nhds (1/2)) ∧
    ¬ {n : ℕ | Erdos218L1.d (n+1) = Erdos218L1.d n}.Infinite := by
  refine ⟨Erdos218L1.densityLE, Erdos218L1.densityGE, ?_⟩
  intro h
  have hE : {n : ℕ | Erdos218L1.d (n+1) = Erdos218L1.d n} = ∅ := by
    ext n; simp [Erdos218L1.eq_cond]
  rw [hE] at h
  exact Set.finite_empty.not_infinite h := by refine ⟨Erdos218L1.densityLE, Erdos218L1.densityGE, ?_⟩; intro h; have hE : {n : ℕ | Erdos218L1.d (n+1) = Erdos218L1.d n} = ∅ := by ext n; simp [Erdos218L1.eq_cond]; rw [hE] at h; exact Set.finite_empty.not_infinite h

-- axiom footprint
#print axioms Erdos218L1.d
#print axioms Erdos218L1.cntLE
#print axioms Erdos218L1.cntGE
#print axioms Erdos218L1.d_val
#print axioms Erdos218L1.le_cond
#print axioms Erdos218L1.ge_cond
#print axioms Erdos218L1.eq_cond
#print axioms Erdos218L1.cntLE_succ
#print axioms Erdos218L1.cntLE_eq
#print axioms Erdos218L1.cntGE_succ
#print axioms Erdos218L1.cntGE_eq
#print axioms Erdos218L1.ratioLE
#print axioms Erdos218L1.ratioGE
#print axioms Erdos218L1.key
#print axioms Erdos218L1.densityLE
#print axioms Erdos218L1.densityGE
#print axioms msl_fmz_erdos218_campaign_001_R005_L1
