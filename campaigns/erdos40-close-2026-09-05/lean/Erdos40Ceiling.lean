/-
  Erdős Problem 40 — an unconditional CEILING on the answer set.

  The source page (erdosproblems.com/40) records no `g` for which the implication is known,
  and no `g` for which it is known to fail.  This file kernel-checks an explicit upper pin:

      NO function `g` with `√N / g(N) = O(log N)` belongs to the answer set.

  The witness is the set of powers of two — an infinite Sidon set with `r_A(n) ≤ 2` and
  counting function `≥ log₂ N + 1`.  In particular `g(N) = √N / log N` tends to infinity and
  is NOT an answer, and by downward closure neither is any faster-growing `g`.

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Erdos40Core

namespace Erdos40

open Finset Filter Set Asymptotics
open scoped Topology

attribute [local instance 100] Classical.propDecidable

/-! ## A general criterion for `r_A ≤ 2` -/

/-- If, at `n`, the LARGER element of any representation `n = x + a` (`a ≤ x`, both in `A`)
is uniquely determined, then `r_A(n) ≤ 2`. -/
theorem rep_le_two_of_max_unique {A : Set ℕ} {n : ℕ}
    (h : ∀ x a y b : ℕ, x ∈ A → a ∈ A → y ∈ A → b ∈ A →
      x + a = n → y + b = n → a ≤ x → b ≤ y → x = y) :
    rep A n ≤ 2 := by
  classical
  rcases Finset.eq_empty_or_nonempty
      ((Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)) with he | ⟨q, hq⟩
  · simp [rep, he]
  · have hqm := hq
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at hqm
    obtain ⟨hqn, hq1, hq2⟩ := hqm
    have hsub : (Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)
        ⊆ ({q, (q.2, q.1)} : Finset (ℕ × ℕ)) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_antidiagonal] at hp
      obtain ⟨hpn, hp1, hp2⟩ := hp
      have key : (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1) := by
        rcases le_total p.2 p.1 with h1 | h1 <;> rcases le_total q.2 q.1 with h2 | h2
        · have hx := h p.1 p.2 q.1 q.2 hp1 hp2 hq1 hq2 hpn hqn h1 h2
          exact Or.inl ⟨hx, by omega⟩
        · have hx := h p.1 p.2 q.2 q.1 hp1 hp2 hq2 hq1 hpn (by omega) h1 h2
          exact Or.inr ⟨hx, by omega⟩
        · have hx := h p.2 p.1 q.1 q.2 hp2 hp1 hq1 hq2 (by omega) hqn h1 h2
          exact Or.inr ⟨by omega, hx⟩
        · have hx := h p.2 p.1 q.2 q.1 hp2 hp1 hq2 hq1 (by omega) (by omega) h1 h2
          exact Or.inl ⟨by omega, hx⟩
      obtain ⟨p1, p2⟩ := p
      obtain ⟨q1, q2⟩ := q
      dsimp only at key
      rcases key with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2 <;> simp
    calc rep A n = ((Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card := rfl
      _ ≤ ({q, (q.2, q.1)} : Finset (ℕ × ℕ)).card := Finset.card_le_card hsub
      _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)

/-! ## Sidon sets in the standard sense -/

/-- `A` is a Sidon set (`B₂` set): `a + b = c + d` with all four in `A` forces the unordered
pairs to agree.  This is the textbook definition. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A → a + b = c + d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A Sidon set has `r_A(n) ≤ 2` for every `n`. -/
theorem rep_le_two_of_isSidon {A : Set ℕ} (h : IsSidon A) (n : ℕ) : rep A n ≤ 2 := by
  refine rep_le_two_of_max_unique ?_
  intro x a y b hx ha hy hb hxa hyb hax hby
  rcases h x a y b hx ha hy hb (by omega) with ⟨e1, _⟩ | ⟨e1, e2⟩
  · exact e1
  · omega

/-! ## The witness: powers of two -/

/-- The set of powers of two. -/
def P2 : Set ℕ := {n : ℕ | ∃ k : ℕ, n = 2 ^ k}

/-- **The key arithmetic fact about powers of two.**  If `2^i + 2^a = 2^j + 2^b` with
`2^a ≤ 2^i` and `2^b ≤ 2^j`, then `2^i = 2^j`: otherwise, say `i < j`, and
`2^i + 2^a ≤ 2^{i+1} ≤ 2^j < 2^j + 2^b`, contradicting equality. -/
theorem P2_max_unique {n : ℕ} : ∀ x a y b : ℕ, x ∈ P2 → a ∈ P2 → y ∈ P2 → b ∈ P2 →
    x + a = n → y + b = n → a ≤ x → b ≤ y → x = y := by
  intro x a y b hx ha hy hb hxa hyb hax hby
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨ai, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hy
  obtain ⟨bi, rfl⟩ := hb
  have hposa : 0 < (2 : ℕ) ^ ai := pow_pos (by norm_num) ai
  have hposb : 0 < (2 : ℕ) ^ bi := pow_pos (by norm_num) bi
  rcases lt_trichotomy i j with hij | hij | hij
  · exfalso
    have e1 : (2 : ℕ) ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ]; ring
    have h1 : (2 : ℕ) ^ i + 2 ^ ai ≤ 2 ^ (i + 1) := by
      rw [e1]; exact Nat.add_le_add_left hax _
    have h2 : (2 : ℕ) ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hij
    have : n < n := by
      calc n = 2 ^ i + 2 ^ ai := hxa.symm
        _ ≤ 2 ^ (i + 1) := h1
        _ ≤ 2 ^ j := h2
        _ < 2 ^ j + 2 ^ bi := by omega
        _ = n := hyb
    exact absurd this (lt_irrefl n)
  · rw [hij]
  · exfalso
    have e1 : (2 : ℕ) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
    have h1 : (2 : ℕ) ^ j + 2 ^ bi ≤ 2 ^ (j + 1) := by
      rw [e1]; exact Nat.add_le_add_left hby _
    have h2 : (2 : ℕ) ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hij
    have : n < n := by
      calc n = 2 ^ j + 2 ^ bi := hyb.symm
        _ ≤ 2 ^ (j + 1) := h1
        _ ≤ 2 ^ i := h2
        _ < 2 ^ i + 2 ^ ai := by omega
        _ = n := hxa
    exact absurd this (lt_irrefl n)

/-- **The powers of two form a Sidon set** in the textbook sense. -/
theorem P2_isSidon : IsSidon P2 := by
  intro a b c d ha hb hc hd habcd
  rcases le_total b a with h1 | h1 <;> rcases le_total d c with h2 | h2
  · have := P2_max_unique (n := a + b) a b c d ha hb hc hd rfl (by omega) h1 h2
    exact Or.inl ⟨this, by omega⟩
  · have := P2_max_unique (n := a + b) a b d c ha hb hd hc rfl (by omega) h1 h2
    exact Or.inr ⟨this, by omega⟩
  · have := P2_max_unique (n := a + b) b a c d hb ha hc hd (by omega) (by omega) h1 h2
    exact Or.inr ⟨by omega, this⟩
  · have := P2_max_unique (n := a + b) b a d c hb ha hd hc (by omega) (by omega) h1 h2
    exact Or.inl ⟨by omega, this⟩

/-- `r_{P2}(n) ≤ 2` for every `n`. -/
theorem rep_P2_le_two (n : ℕ) : rep P2 n ≤ 2 :=
  rep_le_two_of_isSidon P2_isSidon n

/-- **The powers of two are logarithmically dense**: `|P2 ∩ [1,N]| ≥ log₂ N + 1` for `N ≥ 1`. -/
theorem cnt_P2_ge (N : ℕ) (hN : 1 ≤ N) : Nat.log 2 N + 1 ≤ cnt P2 N := by
  classical
  have hsub : ((Finset.range (Nat.log 2 N + 1)).image (fun k => 2 ^ k))
      ⊆ (Finset.Icc 1 N).filter (fun a => a ∈ P2) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range] at hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ (by norm_num), ?_⟩,
      ⟨k, rfl⟩⟩
    calc (2 : ℕ) ^ k ≤ 2 ^ (Nat.log 2 N) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hcard : ((Finset.range (Nat.log 2 N + 1)).image (fun k => 2 ^ k)).card
      = Nat.log 2 N + 1 := by
    rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (le_refl 2)),
      Finset.card_range]
  rw [cnt, ← hcard]
  exact Finset.card_le_card hsub

/-- `log N = O(|P2 ∩ [1,N]|)`. -/
theorem log_isBigO_cnt_P2 :
    (fun N : ℕ => Real.log (N : ℝ)) =O[atTop]
      (fun N : ℕ => ((P2 ∩ Set.Icc 1 N).ncard : ℝ)) := by
  refine IsBigO.of_bound (Real.log 2) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hcast : (N : ℝ) ≤ ((2 : ℝ)) ^ (Nat.log 2 N + 1) := by
    have : ((N : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 N + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
    simpa using this
  have h1 : Real.log (N : ℝ) ≤ ((Nat.log 2 N : ℝ) + 1) * Real.log 2 := by
    have hstep : Real.log (N : ℝ) ≤ Real.log (((2 : ℝ)) ^ (Nat.log 2 N + 1)) :=
      (Real.log_le_log_iff hNpos (by positivity)).mpr hcast
    rw [Real.log_pow] at hstep
    push_cast at hstep
    linarith
  have h2 : ((Nat.log 2 N : ℝ) + 1) ≤ ((P2 ∩ Set.Icc 1 N).ncard : ℝ) := by
    rw [ncard_eq_cnt]
    have := cnt_P2_ge N hN
    exact_mod_cast this
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogN,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ((P2 ∩ Set.Icc 1 N).ncard : ℝ))]
  calc Real.log (N : ℝ) ≤ ((Nat.log 2 N : ℝ) + 1) * Real.log 2 := h1
    _ = Real.log 2 * ((Nat.log 2 N : ℝ) + 1) := mul_comm _ _
    _ ≤ Real.log 2 * ((P2 ∩ Set.Icc 1 N).ncard : ℝ) := mul_le_mul_of_nonneg_left h2 hlog2

/-! ## The ceiling -/

/-- **CEILING THEOREM.**  No `g` whose threshold `√N / g(N)` is `O(log N)` can be an answer
to Erdős 40.  The powers of two are a Sidon set that is too dense for such a `g`. -/
theorem not_erdos40For_of_thr_isBigO_log {g : ℕ → ℝ}
    (h : (fun N : ℕ => Real.sqrt (N : ℝ) / g N) =O[atTop] (fun N : ℕ => Real.log (N : ℝ))) :
    ¬ Erdos40For g :=
  not_erdos40For_of_bounded_witness (A := P2) (B := 2) rep_P2_le_two
    (h.trans log_isBigO_cnt_P2)

/-- **The explicit excluded function.**  `g(N) = √N / log N` is not an answer. -/
theorem not_erdos40For_sqrt_div_log :
    ¬ Erdos40For (fun N : ℕ => Real.sqrt (N : ℝ) / Real.log (N : ℝ)) := by
  refine not_erdos40For_of_thr_isBigO_log ?_
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hs : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hl : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hrw : Real.sqrt (N : ℝ) / (Real.sqrt (N : ℝ) / Real.log (N : ℝ))
      = Real.log (N : ℝ) := by
    field_simp
  rw [hrw, one_mul]

/-- `g(N) = √N / log N` really does tend to infinity, so the ceiling excludes a function of
the kind Erdős 40 asks about. -/
theorem tendsto_sqrt_div_log_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) / Real.log (N : ℝ)) atTop atTop := by
  have h0 : Real.log =o[atTop] fun x : ℝ => x ^ (1 / (2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / (2 : ℝ))) atTop (𝓝 0) :=
    h0.tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / (2 : ℝ))) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hp : (0 : ℝ) < x ^ (1 / (2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    exact Set.mem_Ioi.mpr (div_pos hlog hp)
  have h3 := h2.inv_tendsto_nhdsGT_zero
  have h4 : Tendsto (fun x : ℝ => Real.sqrt x / Real.log x) atTop atTop := by
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Pi.inv_apply, inv_div, Real.sqrt_eq_rpow]
  exact h4.comp tendsto_natCast_atTop_atTop

/-- **The ceiling, in answer-set form.**  Every member `g` of the answer set of Erdős 40 must
have its threshold `√N / g(N)` NOT dominated by `log N`. -/
theorem answer_set_ceiling {g : ℕ → ℝ} (H : Erdos40For g) :
    ¬ ((fun N : ℕ => Real.sqrt (N : ℝ) / g N) =O[atTop] (fun N : ℕ => Real.log (N : ℝ))) :=
  fun h => not_erdos40For_of_thr_isBigO_log h H

/-- **The answer set is capped by how dense an infinite Sidon set can be.**  Any Sidon set
whose counting function dominates the threshold `√N / g(N)` knocks `g` out of the answer set.
This is the precise point at which Erdős 40 meets the (open) question of how dense an infinite
Sidon set can be; the powers of two are the elementary instance, giving the `log N` ceiling
above, and every improvement in Sidon-set density lowers the ceiling automatically. -/
theorem not_erdos40For_of_dense_sidon {g : ℕ → ℝ} {A : Set ℕ} (hA : IsSidon A)
    (hdens : (fun N : ℕ => Real.sqrt (N : ℝ) / g N) =O[atTop]
      (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ))) :
    ¬ Erdos40For g :=
  not_erdos40For_of_bounded_witness (rep_le_two_of_isSidon hA) hdens

end Erdos40
