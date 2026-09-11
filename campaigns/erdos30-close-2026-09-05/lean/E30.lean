import Mathlib

/-!
# Erdős Problem 30 — Part 1: definitions and the trivial bound

Target: https://www.erdosproblems.com/30  ($1000, OPEN)
Lean statement lives in google-deepmind/formal-conjectures at
`FormalConjectures/ErdosProblems/30.lean`, which reads

    noncomputable abbrev h (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)
    theorem erdos_30 : answer(sorry) ↔
        ∀ᵉ (ε > 0), (fun N => h N - (N : Real).sqrt) =O[atTop] fun N => (N : ℝ)^(ε : ℝ)
    -- TODO(firsching): add the various known bounds as variants.

This file discharges part of that TODO.  The definitions `IsSidon` and
`maxSidonSubsetCard` are copied VERBATIM from
`FormalConjecturesForMathlib/Combinatorics/Basic.lean` so that the results here
are about exactly the same object as `Erdos30.h`.
-/

namespace E30

open Finset

variable {α : Type*} [AddCommMonoid α]

/-- A Sidon set is a set such that all pairwise sums of elements are distinct apart from
coincidences forced by the commutativity of addition.
VERBATIM from `FormalConjecturesForMathlib/Combinatorics/Basic.lean`. -/
def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

instance (A : Finset α) [DecidableEq α] : Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

/-- The maximum size of a Sidon set in the supplied `Finset`.
VERBATIM from `FormalConjecturesForMathlib/Combinatorics/Basic.lean`. -/
def maxSidonSubsetCard (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

/-- `h N`, exactly as in `FormalConjectures/ErdosProblems/30.lean`. -/
noncomputable abbrev h (N : ℕ) : ℕ := maxSidonSubsetCard (Finset.Icc 1 N)

/-! ### The maximum is attained -/

/-- `maxSidonSubsetCard` is attained by an actual Sidon subset. -/
theorem exists_sidon_card_eq (A : Finset ℕ) :
    ∃ B ⊆ A, IsSidon (B : Set ℕ) ∧ B.card = maxSidonSubsetCard A := by
  classical
  have hne : (A.powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ)).Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [mem_filter, mem_powerset]
    exact ⟨empty_subset _, by intro i₁ h₁; simp at h₁⟩
  obtain ⟨B, hB, hBsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [mem_filter, mem_powerset] at hB
  exact ⟨B, hB.1, hB.2, hBsup.symm⟩

/-! ### Sidon sets have injective difference map -/

/-- The set of strictly increasing pairs from `A`. -/
def upairs (A : Finset ℕ) : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 < p.2)

/-- **The Sidon property in difference form.** On strictly increasing pairs of a Sidon set the
map `(a, b) ↦ b - a` is injective. -/
theorem sidon_diff_injOn {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) :
    Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) (upairs A) := by
  rintro ⟨a, b⟩ hp ⟨c, d⟩ hq hpq
  simp only [upairs, coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp hq
  obtain ⟨⟨ha, hb⟩, hab⟩ := hp
  obtain ⟨⟨hc, hd⟩, hcd⟩ := hq
  simp only at hpq
  -- `b - a = d - c` with `a < b`, `c < d` gives `b + c = d + a`
  have key : b + c = d + a := by omega
  have := hA b (by exact_mod_cast hb) d (by exact_mod_cast hd)
      c (by exact_mod_cast hc) a (by exact_mod_cast ha) key
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · omega

/-! ### The trivial bound `k² ≤ 2N + k` -/

/-- Counting the `k(k-1)/2` distinct positive differences of a Sidon set inside `{1,…,N}`. -/
theorem card_sq_le (N : ℕ) {A : Finset ℕ} (hAN : A ⊆ Finset.Icc 1 N)
    (hA : IsSidon (A : Set ℕ)) : A.card ^ 2 ≤ 2 * N + A.card := by
  classical
  -- the image of `upairs A` under the difference map lands in `Icc 1 N`
  have himg : (upairs A).image (fun p : ℕ × ℕ => p.2 - p.1) ⊆ Finset.Icc 1 N := by
    intro d hd
    simp only [mem_image, upairs, mem_filter, Finset.mem_product] at hd
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hab⟩, rfl⟩ := hd
    have ha' := hAN ha
    have hb' := hAN hb
    simp only [Finset.mem_Icc] at ha' hb' ⊢
    omega
  have hcard : (upairs A).card ≤ N := by
    calc (upairs A).card
        = ((upairs A).image (fun p : ℕ × ℕ => p.2 - p.1)).card :=
          (Finset.card_image_of_injOn (sidon_diff_injOn hA)).symm
      _ ≤ (Finset.Icc 1 N).card := Finset.card_le_card himg
      _ = N := by simp
  -- `2 * |upairs A| + |A| = |A|^2`
  have hsplit : 2 * (upairs A).card + A.card = A.card ^ 2 := by
    have h1 : (A ×ˢ A).card = A.card ^ 2 := by
      rw [Finset.card_product]; ring
    have h2 : ((A ×ˢ A).filter (fun p => p.1 < p.2)).card
        = ((A ×ˢ A).filter (fun p => p.2 < p.1)).card := by
      apply Finset.card_bij' (fun p _ => Prod.swap p) (fun p _ => Prod.swap p)
      · rintro ⟨a, b⟩ hp
        simp only [mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · rintro ⟨a, b⟩ hp
        simp only [mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · rintro ⟨a, b⟩ _; rfl
      · rintro ⟨a, b⟩ _; rfl
    have h3 : ((A ×ˢ A).filter (fun p => p.1 = p.2)).card = A.card := by
      have hdiag : (A ×ˢ A).filter (fun p => p.1 = p.2) = A.diag := by
        ext p
        simp only [mem_filter, Finset.mem_product, Finset.mem_diag]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ h1⟩, h2⟩
      rw [hdiag, Finset.diag_card]
    have hpart : ((A ×ˢ A).filter (fun p => p.1 < p.2)).card
        + ((A ×ˢ A).filter (fun p => p.2 < p.1)).card
        + ((A ×ˢ A).filter (fun p => p.1 = p.2)).card = (A ×ˢ A).card := by
      classical
      rw [← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
      · congr 1
        ext p
        simp only [Finset.mem_union, mem_filter]
        constructor
        · rintro ((h | h) | h) <;> exact h.1
        · intro hp
          rcases lt_trichotomy p.1 p.2 with h | h | h
          · exact Or.inl (Or.inl ⟨hp, h⟩)
          · exact Or.inr ⟨hp, h⟩
          · exact Or.inl (Or.inr ⟨hp, h⟩)
      · rw [Finset.disjoint_left]
        intro p hp hq
        simp only [Finset.mem_union, mem_filter] at hp hq
        rcases hp with h | h <;> omega
      · rw [Finset.disjoint_left]
        intro p hp hq
        simp only [mem_filter] at hp hq
        omega
    simp only [upairs]
    omega
  omega

/-! ### Window counts -/

/-- `wc A ℓ u` = number of elements of `A` in the window `(u - ℓ, u]`. -/
def wc (A : Finset ℕ) (ℓ u : ℕ) : ℕ := (A.filter (fun a => a ≤ u ∧ u < a + ℓ)).card

/-- `pc U ℓ a b` = number of windows (indexed by `U`) containing both `a` and `b`. -/
def pc (U : Finset ℕ) (ℓ a b : ℕ) : ℕ :=
  (U.filter (fun u => (a ≤ u ∧ u < a + ℓ) ∧ (b ≤ u ∧ u < b + ℓ))).card

theorem pc_comm (U : Finset ℕ) (ℓ a b : ℕ) : pc U ℓ a b = pc U ℓ b a := by
  unfold pc
  congr 1
  ext u
  simp only [Finset.mem_filter]
  tauto

theorem pc_le_len (U : Finset ℕ) (ℓ a b : ℕ) : pc U ℓ a b ≤ ℓ := by
  unfold pc
  calc (U.filter (fun u => (a ≤ u ∧ u < a + ℓ) ∧ (b ≤ u ∧ u < b + ℓ))).card
      ≤ (Finset.Ico a (a + ℓ)).card := by
        apply Finset.card_le_card
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_Ico] at hu ⊢
        omega
    _ = ℓ := by rw [Nat.card_Ico]; omega

theorem pc_le_gap (U : Finset ℕ) (ℓ a b : ℕ) (hab : a < b) : pc U ℓ a b ≤ ℓ - (b - a) := by
  unfold pc
  calc (U.filter (fun u => (a ≤ u ∧ u < a + ℓ) ∧ (b ≤ u ∧ u < b + ℓ))).card
      ≤ (Finset.Ico b (a + ℓ)).card := by
        apply Finset.card_le_card
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_Ico] at hu ⊢
        omega
    _ = ℓ - (b - a) := by rw [Nat.card_Ico]; omega

/-! ### Step 1 : the first moment is exactly `k * ℓ` -/

theorem sum_wc (N ℓ : ℕ) {A : Finset ℕ} (hAN : A ⊆ Finset.Icc 1 N) :
    ∑ u ∈ Finset.Icc 1 (N + ℓ), wc A ℓ u = A.card * ℓ := by
  classical
  simp only [wc, Finset.card_filter]
  rw [Finset.sum_comm]
  have key : ∀ a ∈ A, (∑ u ∈ Finset.Icc 1 (N + ℓ), if (a ≤ u ∧ u < a + ℓ) then 1 else 0) = ℓ := by
    intro a ha
    rw [← Finset.card_filter]
    have hset : (Finset.Icc 1 (N + ℓ)).filter (fun u => a ≤ u ∧ u < a + ℓ)
        = Finset.Ico a (a + ℓ) := by
      have ha' := hAN ha
      simp only [Finset.mem_Icc] at ha'
      ext u
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset, Nat.card_Ico]
    omega
  rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul]

/-! ### Step 2 : the second moment as a pair count -/

theorem sum_wc_sq (A U : Finset ℕ) (ℓ : ℕ) :
    ∑ u ∈ U, (wc A ℓ u) ^ 2 = ∑ a ∈ A, ∑ b ∈ A, pc U ℓ a b := by
  classical
  have expand : ∀ u : ℕ, (wc A ℓ u) ^ 2
      = ∑ a ∈ A, ∑ b ∈ A, if ((a ≤ u ∧ u < a + ℓ) ∧ (b ≤ u ∧ u < b + ℓ)) then 1 else 0 := by
    intro u
    simp only [wc, Finset.card_filter, sq]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp_all
  simp only [expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.card_filter]
  rfl

/-! ### Step 3 : the triangular sum -/

theorem sum_gap_le (ℓ : ℕ) : 2 * (∑ d ∈ Finset.Ico 1 ℓ, (ℓ - d)) ≤ ℓ * ℓ := by
  classical
  have hinj : ∀ x ∈ Finset.Ico 1 ℓ, ∀ y ∈ Finset.Ico 1 ℓ, ℓ - x = ℓ - y → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_Ico] at hx hy
    omega
  have himg : (Finset.Ico 1 ℓ).image (fun d => ℓ - d) = Finset.Ico 1 ℓ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨d, hd, rfl⟩
      omega
    · intro hx
      exact ⟨ℓ - x, by omega, by omega⟩
  have hswap : (∑ d ∈ Finset.Ico 1 ℓ, (ℓ - d)) = ∑ d ∈ Finset.Ico 1 ℓ, d := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image hinj]
  have hrange : (∑ d ∈ Finset.Ico 1 ℓ, d) = ∑ d ∈ Finset.range ℓ, d := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
      omega
    · intro x hx hnx
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_Ico] at hnx
      omega
  rw [hswap, hrange]
  have hg := Finset.sum_range_id_mul_two ℓ
  have hmono : ℓ * (ℓ - 1) ≤ ℓ * ℓ := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  omega

/-! ### Step 4 : the off-diagonal pair count is at most `ℓ * ℓ` -/

theorem sum_upairs_le {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (U : Finset ℕ) (ℓ : ℕ) :
    ∑ p ∈ upairs A, pc U ℓ p.1 p.2 ≤ ∑ d ∈ Finset.Ico 1 ℓ, (ℓ - d) := by
  classical
  set S := (upairs A).image (fun p : ℕ × ℕ => p.2 - p.1) with hS
  have hSpos : ∀ d ∈ S, 1 ≤ d := by
    intro d hd
    simp only [hS, Finset.mem_image, upairs, Finset.mem_filter, Finset.mem_product] at hd
    obtain ⟨⟨a, b⟩, ⟨_, hab⟩, rfl⟩ := hd
    simp only at hab ⊢
    omega
  have step1 : ∑ p ∈ upairs A, pc U ℓ p.1 p.2 ≤ ∑ p ∈ upairs A, (ℓ - (p.2 - p.1)) := by
    apply Finset.sum_le_sum
    rintro ⟨a, b⟩ hp
    simp only [upairs, Finset.mem_filter, Finset.mem_product] at hp
    exact pc_le_gap U ℓ a b hp.2
  have step2 : ∑ p ∈ upairs A, (ℓ - (p.2 - p.1)) = ∑ d ∈ S, (ℓ - d) := by
    rw [hS, Finset.sum_image]
    intro x hx y hy hxy
    exact sidon_diff_injOn hA (by simpa using hx) (by simpa using hy) hxy
  have step3 : ∑ d ∈ S, (ℓ - d) = ∑ d ∈ S.filter (fun d => d < ℓ), (ℓ - d) := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro x _ hx
    omega
  have step4 : S.filter (fun d => d < ℓ) ⊆ Finset.Ico 1 ℓ := by
    intro d hd
    simp only [Finset.mem_filter] at hd
    simp only [Finset.mem_Ico]
    exact ⟨hSpos d hd.1, hd.2⟩
  calc ∑ p ∈ upairs A, pc U ℓ p.1 p.2
      ≤ ∑ p ∈ upairs A, (ℓ - (p.2 - p.1)) := step1
    _ = ∑ d ∈ S, (ℓ - d) := step2
    _ = ∑ d ∈ S.filter (fun d => d < ℓ), (ℓ - d) := step3
    _ ≤ ∑ d ∈ Finset.Ico 1 ℓ, (ℓ - d) := Finset.sum_le_sum_of_subset step4

/-- The mirror-image sum over strictly decreasing pairs. -/
theorem sum_dpairs_eq (A U : Finset ℕ) (ℓ : ℕ) :
    ∑ p ∈ (A ×ˢ A).filter (fun p => p.2 < p.1), pc U ℓ p.1 p.2
      = ∑ p ∈ upairs A, pc U ℓ p.1 p.2 := by
  classical
  apply Finset.sum_nbij' (fun p => Prod.swap p) (fun p => Prod.swap p)
  · rintro ⟨a, b⟩ hp
    simp only [upairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  · rintro ⟨a, b⟩ hp
    simp only [upairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  · rintro ⟨a, b⟩ _; rfl
  · rintro ⟨a, b⟩ _; rfl
  · rintro ⟨a, b⟩ _
    exact pc_comm U ℓ a b

/-! ### Step 5 : Cauchy–Schwarz over ℕ -/

theorem nat_cauchy_schwarz (U : Finset ℕ) (F : ℕ → ℕ) :
    (∑ u ∈ U, F u) ^ 2 ≤ U.card * ∑ u ∈ U, (F u) ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) (fun u => (F u : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hcast : ((∑ u ∈ U, F u : ℕ) : ℝ) ^ 2 ≤ ((U.card * ∑ u ∈ U, (F u) ^ 2 : ℕ) : ℝ) := by
    push_cast
    convert h using 2
  exact_mod_cast hcast

/-! ### The main inequality -/

/-- **Erdős–Turán window inequality.** If `A ⊆ {1,…,N}` is a Sidon set then for every
window length `ℓ ≥ 1`,
`|A|² · ℓ ≤ (N + ℓ)(|A| + ℓ)`. -/
theorem sidon_key (N ℓ : ℕ) (hℓ : 0 < ℓ) {A : Finset ℕ} (hAN : A ⊆ Finset.Icc 1 N)
    (hA : IsSidon (A : Set ℕ)) : A.card ^ 2 * ℓ ≤ (N + ℓ) * (A.card + ℓ) := by
  classical
  set U := Finset.Icc 1 (N + ℓ) with hU
  have hUcard : U.card = N + ℓ := by simp [hU]
  -- first moment
  have h1 : ∑ u ∈ U, wc A ℓ u = A.card * ℓ := sum_wc N ℓ hAN
  -- second moment split
  have hsplit : ∑ a ∈ A, ∑ b ∈ A, pc U ℓ a b
      = ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 = p.2), pc U ℓ p.1 p.2
      + (∑ p ∈ upairs A, pc U ℓ p.1 p.2
        + ∑ p ∈ (A ×ˢ A).filter (fun p => p.2 < p.1), pc U ℓ p.1 p.2) := by
    rw [← Finset.sum_product']
    rw [← Finset.sum_filter_add_sum_filter_not (A ×ˢ A) (fun p => p.1 = p.2)]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not
      ((A ×ˢ A).filter (fun p => ¬ p.1 = p.2)) (fun p => p.1 < p.2)]
    congr 1
    · congr 1
      ext p
      simp only [upairs, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp, _⟩, h⟩; exact ⟨hp, h⟩
      · rintro ⟨hp, h⟩; exact ⟨⟨hp, by omega⟩, h⟩
    · congr 1
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp, hne⟩, h⟩; exact ⟨hp, by omega⟩
      · rintro ⟨hp, h⟩; exact ⟨⟨hp, by omega⟩, by omega⟩
  -- diagonal ≤ |A| * ℓ
  have hdiag : ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 = p.2), pc U ℓ p.1 p.2 ≤ A.card * ℓ := by
    have hcard : ((A ×ˢ A).filter (fun p => p.1 = p.2)).card = A.card := by
      have hd : (A ×ˢ A).filter (fun p => p.1 = p.2) = A.diag := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_diag]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ h1⟩, h2⟩
      rw [hd, Finset.diag_card]
    calc ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 = p.2), pc U ℓ p.1 p.2
        ≤ ∑ _p ∈ (A ×ˢ A).filter (fun p => p.1 = p.2), ℓ :=
          Finset.sum_le_sum fun p _ => pc_le_len U ℓ p.1 p.2
      _ = A.card * ℓ := by rw [Finset.sum_const, smul_eq_mul, hcard]
  -- second moment bound
  have h2 : ∑ u ∈ U, (wc A ℓ u) ^ 2 ≤ A.card * ℓ + ℓ * ℓ := by
    rw [sum_wc_sq A U ℓ, hsplit, sum_dpairs_eq A U ℓ]
    have hup := sum_upairs_le hA U ℓ
    have htri := sum_gap_le ℓ
    omega
  -- Cauchy–Schwarz
  have hcs := nat_cauchy_schwarz U (wc A ℓ)
  rw [h1, hUcard] at hcs
  have hchain : (A.card * ℓ) ^ 2 ≤ (N + ℓ) * (A.card * ℓ + ℓ * ℓ) :=
    le_trans hcs (Nat.mul_le_mul_left _ h2)
  -- cancel one factor of ℓ
  have hfinal : (A.card ^ 2 * ℓ) * ℓ ≤ ((N + ℓ) * (A.card + ℓ)) * ℓ := by
    calc (A.card ^ 2 * ℓ) * ℓ = (A.card * ℓ) ^ 2 := by ring
      _ ≤ (N + ℓ) * (A.card * ℓ + ℓ * ℓ) := hchain
      _ = ((N + ℓ) * (A.card + ℓ)) * ℓ := by ring
  exact Nat.le_of_mul_le_mul_right hfinal hℓ


/-! ### Part 3 : the Erdős–Turán upper bound `h N ≤ √N + O(N^(1/4))`

Instantiating `sidon_key` at window length `ℓ = m³` where `m = ⌊N^(1/4)⌋ + 1`.
-/

/-- **The Erdős–Turán / Lindström upper bound, `ℕ` form.**

`h N ≤ ⌊√N⌋ + 3(⌊N^(1/4)⌋ + 1)`.

This is the `√N + O(N^(1/4))` bound.  Erdős problem 30 asks whether the error term can be
improved to `O_ε(N^ε)`; that question is NOT answered here. -/
theorem h_le (N : ℕ) : h N ≤ Nat.sqrt N + 3 * (Nat.sqrt (Nat.sqrt N) + 1) := by
  obtain ⟨B, hBsub, hBsidon, hBcard⟩ := exists_sidon_card_eq (Finset.Icc 1 N)
  show maxSidonSubsetCard (Finset.Icc 1 N) ≤ _
  rw [← hBcard]
  set k := B.card with hkdef
  set s := Nat.sqrt N with hsdef
  set j := Nat.sqrt s with hjdef
  set m := j + 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  -- basic `Nat.sqrt` facts
  have hsN : s * s ≤ N := Nat.sqrt_le N
  have hNs : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
  have hjs : j * j ≤ s := Nat.sqrt_le s
  have hsj : s < (j + 1) * (j + 1) := Nat.lt_succ_sqrt s
  -- `N < m⁴`
  have hN4 : N < (m * m) * (m * m) := by
    have h1 : s + 1 ≤ m * m := by rw [hmdef]; omega
    nlinarith [hNs, h1]
  -- the trivial bound
  have htriv : k ^ 2 ≤ 2 * N + k := card_sq_le N hBsub hBsidon
  -- hence `k ≤ 2m²`
  have hk2m : k ≤ 2 * (m * m) := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [htriv, hN4, hcon, hm1]
  -- the window inequality at `ℓ = m³`
  have hkey : k ^ 2 * (m * m * m) ≤ (N + m * m * m) * (k + m * m * m) :=
    sidon_key N (m * m * m) (by positivity) hBsub hBsidon
  -- `N·k ≤ 2m⁶`
  have hNk : N * k ≤ 2 * (m * m * m * m * m * m) := by
    have h1 : N * k ≤ ((m * m) * (m * m)) * (2 * (m * m)) :=
      Nat.mul_le_mul hN4.le hk2m
    nlinarith [h1]
  -- divide the window inequality by `m³`
  have hmul : k ^ 2 * (m * m * m) ≤ (N + k + 3 * (m * m * m)) * (m * m * m) := by
    nlinarith [hkey, hNk]
  have hdiv : k ^ 2 ≤ N + k + 3 * (m * m * m) :=
    Nat.le_of_mul_le_mul_right hmul (by positivity)
  -- conclude
  by_contra hcon
  rw [not_le] at hcon
  have hge : s + 3 * j + 4 ≤ k := by rw [hmdef] at hcon; omega
  have hkk : (s + 3 * j + 4) * (s + 3 * j + 4) ≤ k * k := Nat.mul_le_mul hge hge
  have hsj3 : j * j * j ≤ s * j := Nat.mul_le_mul_right j hjs
  have hNub : N ≤ s * s + 2 * s := by nlinarith [hNs]
  rw [hmdef] at hdiv hk2m
  nlinarith [hdiv, hkk, hsj3, hNub, hk2m, hjs]

/-- **The Erdős–Turán upper bound, real form.**

`h N ≤ √N + 3·N^(1/4) + 3`.

⛔ NOT PROVED HERE and NOT claimed: the matching lower bound `h N ≥ √N - O(N^θ)`
(Singer difference sets + prime gaps), and the conjecture of Erdős problem 30 itself. -/
theorem h_le_real (N : ℕ) :
    (h N : ℝ) ≤ Real.sqrt N + 3 * (N : ℝ) ^ ((1 : ℝ) / 4) + 3 := by
  have hnat := h_le N
  have hs : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hj4 : (Nat.sqrt (Nat.sqrt N)) ^ 4 ≤ N := by
    have h1 : Nat.sqrt (Nat.sqrt N) * Nat.sqrt (Nat.sqrt N) ≤ Nat.sqrt N := Nat.sqrt_le _
    have h2 : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
    nlinarith [h1, h2, Nat.zero_le (Nat.sqrt (Nat.sqrt N))]
  have hj : ((Nat.sqrt (Nat.sqrt N) : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
    set j : ℕ := Nat.sqrt (Nat.sqrt N) with hjd
    have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    have hpow : ((j : ℝ)) ^ (4 : ℕ) ≤ (N : ℝ) := by exact_mod_cast hj4
    have hquart : ((1 : ℝ) / 4) = (((4 : ℕ) : ℝ))⁻¹ := by norm_num
    calc (j : ℝ) = (((j : ℝ) ^ (4 : ℕ)) ^ (((4 : ℕ) : ℝ))⁻¹) :=
          (Real.pow_rpow_inv_natCast hjnn (by norm_num)).symm
      _ ≤ ((N : ℝ)) ^ (((4 : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hpow (by positivity)
      _ = (N : ℝ) ^ ((1 : ℝ) / 4) := by rw [hquart]
  have hcast : ((h N : ℕ) : ℝ)
      ≤ ((Nat.sqrt N : ℕ) : ℝ) + 3 * ((Nat.sqrt (Nat.sqrt N) : ℕ) : ℝ) + 3 := by
    have h2 : ((h N : ℕ) : ℝ)
        ≤ ((Nat.sqrt N + 3 * (Nat.sqrt (Nat.sqrt N) + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at h2
    linarith
  linarith [hcast, hs, hj]

set_option maxHeartbeats 1000000

/-! ### Part 4 : sharpening the constant — Lindström's `√N + N^(1/4) + O(1)`

Part 3 chose the window length crudely (`ℓ = m³`, `m = ⌊N^(1/4)⌋+1`), costing a factor 3
on the `N^(1/4)` term.  Choosing `ℓ ≈ √(N·k)` instead — the value that balances the two
error terms `Nk/ℓ` and `ℓ` — recovers the sharp constant 1, which is Lindström (1969).
-/

/-- The window inequality at the balancing window length `ℓ = ⌊√(N·k)⌋ + 1`. -/
theorem sidon_sq_le_sqrt (N : ℕ) {A : Finset ℕ} (hAN : A ⊆ Finset.Icc 1 N)
    (hA : IsSidon (A : Set ℕ)) :
    A.card ^ 2 ≤ N + A.card + 2 * Nat.sqrt (N * A.card) + 1 := by
  set k := A.card with hkdef
  set t := Nat.sqrt (N * k) with htdef
  have hl : 0 < t + 1 := Nat.succ_pos t
  have hkey := sidon_key N (t + 1) hl hAN hA
  have hNk : N * k < (t + 1) * (t + 1) := by
    rw [htdef]; exact Nat.lt_succ_sqrt (N * k)
  have hstep : k ^ 2 * (t + 1) < (N + k + 2 * (t + 1)) * (t + 1) := by
    nlinarith [hkey, hNk, hl]
  have hlt : k ^ 2 < N + k + 2 * (t + 1) :=
    lt_of_mul_lt_mul_right hstep (Nat.zero_le _)
  omega

/-- **Lindström's upper bound (sharp constant on `N^(1/4)`).**

`h N ≤ ⌊√N⌋ + ⌊N^(1/4)⌋ + 4`.

Compare Lindström (1969): `h(N) < √N + N^(1/4) + 1`.  The `N^(1/4)` coefficient here is 1,
matching the published bound; only the additive constant is looser. -/
theorem h_le_sharp (N : ℕ) : h N ≤ Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 4 := by
  obtain ⟨B, hBsub, hBsidon, hBcard⟩ := exists_sidon_card_eq (Finset.Icc 1 N)
  show maxSidonSubsetCard (Finset.Icc 1 N) ≤ _
  rw [← hBcard]
  set k := B.card with hkdef
  set s := Nat.sqrt N with hsdef
  set j := Nat.sqrt s with hjdef
  have hsN : s * s ≤ N := Nat.sqrt_le N
  have hNs : N ≤ s * s + 2 * s := by have h := Nat.lt_succ_sqrt N; nlinarith [h]
  have hjs : j * j ≤ s := Nat.sqrt_le s
  have hsj : s ≤ j * j + 2 * j := by have h := Nat.lt_succ_sqrt s; nlinarith [h]
  have htriv : k ^ 2 ≤ 2 * N + k := card_sq_le N hBsub hBsidon
  have hfirst : k ≤ s + 3 * j + 3 := by
    have h1 : maxSidonSubsetCard (Finset.Icc 1 N)
        ≤ Nat.sqrt N + 3 * (Nat.sqrt (Nat.sqrt N) + 1) := h_le N
    rw [← hBcard] at h1
    omega
  have hA := sidon_sq_le_sqrt N hBsub hBsidon
  set t := Nat.sqrt (N * k) with htdef
  have ht2 : t * t ≤ N * k := Nat.sqrt_le (N * k)
  by_contra hcon
  rw [not_le] at hcon
  have hge : s + j + 5 ≤ k := by omega
  have hkk : (s + j + 5) * (s + j + 5) ≤ k * k := Nat.mul_le_mul hge hge
  rcases Nat.lt_or_ge s 3 with hsmall | hbig
  · -- `s < 3` forces `N ≤ 8`; the trivial bound already kills it
    have hN8 : N ≤ 8 := by nlinarith [hNs, hsmall]
    nlinarith [htriv, hge, hN8, hkk]
  · -- the main range
    have hlow : 2 * s * j + 7 * s + j * j + 7 * j + 21 ≤ 2 * t := by
      nlinarith [hA, hkk, hfirst, hNs]
    have hNkub : N * k ≤ (s * s + 2 * s) * (s + 3 * j + 3) := Nat.mul_le_mul hNs hfirst
    have hup : t * t ≤ (s * s + 2 * s) * (s + 3 * j + 3) := le_trans ht2 hNkub
    have hlow2 : (2 * s * j + 7 * s + j * j + 7 * j + 21)
        * (2 * s * j + 7 * s + j * j + 7 * j + 21) ≤ (2 * t) * (2 * t) :=
      Nat.mul_le_mul hlow hlow
    have hj1 : 1 ≤ j := by nlinarith [hjs, hbig, hsj]
    -- pure algebra from here: everything is linear in the monomials
    -- s²j², s²j, s³, s², sj, s
    have hcomb : (2 * s * j + 7 * s + j * j + 7 * j + 21)
        * (2 * s * j + 7 * s + j * j + 7 * j + 21)
        ≤ 4 * ((s * s + 2 * s) * (s + 3 * j + 3)) := by
      calc (2 * s * j + 7 * s + j * j + 7 * j + 21)
            * (2 * s * j + 7 * s + j * j + 7 * j + 21)
          ≤ (2 * t) * (2 * t) := hlow2
        _ = 4 * (t * t) := by ring
        _ ≤ 4 * ((s * s + 2 * s) * (s + 3 * j + 3)) := by linarith [hup]
    have e1 : 4 * (s * s * (j * j)) + 28 * (s * (s * j)) + 49 * (s * s)
        ≤ (2 * s * j + 7 * s + j * j + 7 * j + 21)
          * (2 * s * j + 7 * s + j * j + 7 * j + 21) := by
      have expand : (2 * s * j + 7 * s + j * j + 7 * j + 21)
          * (2 * s * j + 7 * s + j * j + 7 * j + 21)
          = (4 * (s * s * (j * j)) + 28 * (s * (s * j)) + 49 * (s * s))
            + (j * j * j * j + 4 * (s * (j * j * j)) + 14 * (j * j * j)
               + 42 * (s * (j * j)) + 91 * (j * j) + 182 * (s * j)
               + 294 * s + 294 * j + 441) := by ring
      rw [expand]
      exact Nat.le_add_right _ _
    have e2 : 4 * ((s * s + 2 * s) * (s + 3 * j + 3))
        = 4 * (s * (s * s)) + 12 * (s * (s * j)) + 20 * (s * s)
          + 24 * (s * j) + 24 * s := by ring
    have e3' : s * s * s ≤ s * s * (j * j + 2 * j) := Nat.mul_le_mul_left (s * s) hsj
    have e3 : 4 * (s * (s * s)) ≤ 4 * (s * s * (j * j)) + 8 * (s * (s * j)) := by
      linarith [e3']
    have e4 : 24 * (s * j) + 24 * s < 8 * (s * (s * j)) + 29 * (s * s) := by
      have h1 : 3 * (s * j) ≤ s * (s * j) := Nat.mul_le_mul_right (s * j) hbig
      have h2 : 3 * s ≤ s * s := Nat.mul_le_mul_right s hbig
      have h3 : 0 < s * s := by positivity
      linarith [h1, h2, h3]
    have e5 : 4 * (s * s * (j * j)) + 28 * (s * (s * j)) + 49 * (s * s)
        ≤ 4 * ((s * s + 2 * s) * (s + 3 * j + 3)) := le_trans e1 hcomb
    rw [e2] at e5
    linarith [e5, e3, e4]


/-- `⌊N^(1/4)⌋ ≤ N^(1/4)` in the reals. -/
theorem cast_quad_root_le (N : ℕ) :
    ((Nat.sqrt (Nat.sqrt N) : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
  set j : ℕ := Nat.sqrt (Nat.sqrt N) with hjd
  have hj4 : j ^ 4 ≤ N := by
    have h1 : j * j ≤ Nat.sqrt N := Nat.sqrt_le _
    have h2 : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
    nlinarith [h1, h2, Nat.zero_le j]
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hpow : ((j : ℝ)) ^ (4 : ℕ) ≤ (N : ℝ) := by exact_mod_cast hj4
  have hquart : ((1 : ℝ) / 4) = (((4 : ℕ) : ℝ))⁻¹ := by norm_num
  calc (j : ℝ) = (((j : ℝ) ^ (4 : ℕ)) ^ (((4 : ℕ) : ℝ))⁻¹) :=
        (Real.pow_rpow_inv_natCast hjnn (by norm_num)).symm
    _ ≤ ((N : ℝ)) ^ (((4 : ℕ) : ℝ))⁻¹ :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = (N : ℝ) ^ ((1 : ℝ) / 4) := by rw [hquart]

/-- **The Erdős–Turán–Lindström upper bound, real form, sharp coefficient.**

`h N ≤ √N + N^(1/4) + 4`.

Compare Lindström (1969): `h(N) < √N + N^(1/4) + 1`. -/
theorem h_le_real_sharp (N : ℕ) :
    (h N : ℝ) ≤ Real.sqrt N + (N : ℝ) ^ ((1 : ℝ) / 4) + 4 := by
  have hnat := h_le_sharp N
  have hs : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hj := cast_quad_root_le N
  have hcast : ((h N : ℕ) : ℝ)
      ≤ ((Nat.sqrt N : ℕ) : ℝ) + ((Nat.sqrt (Nat.sqrt N) : ℕ) : ℝ) + 4 := by
    have h2 : ((h N : ℕ) : ℝ)
        ≤ ((Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 4 : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at h2
    linarith
  linarith [hcast, hs, hj]

/-- **The Erdős problem 30 error term, bounded above.**

Erdős asks whether `h N - √N = O_ε(N^ε)` for every `ε > 0`.  What is PROVED here is the
classical `O(N^(1/4))` upper bound on that error term.

⛔ The Erdős 30 conjecture itself is NOT proved, NOT disproved, and NOT approached here.
⛔ The matching lower bound on `h N` (Singer difference sets + prime gaps) is NOT formalized. -/
theorem erdos30_error_term_upper (N : ℕ) :
    (h N : ℝ) - Real.sqrt N ≤ (N : ℝ) ^ ((1 : ℝ) / 4) + 4 := by
  linarith [h_le_real_sharp N]


end E30
