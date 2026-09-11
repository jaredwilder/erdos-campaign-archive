import Mathlib

/-!
Erdős 949 — the countable analogue at FULL HINDMAN STRENGTH, generalised to k-fold multiples
(campaign erdos949-extend, 2026-09-05).

The sealed `Erdos949HindmanFS.lean` proved (its `erdos949_hindman_full_finite_sums`): for every
sum-free `S ⊆ ℝ` there is an infinite `A ⊆ ℕ⁺` such that for every nonempty finite `T ⊆ A`, both
`∑T ∉ S` and `2·∑T ∉ S`.  That is the `k = 2` case of the theorem here.

`erdos949_hindman_kfold` : for every fixed `k` and every sum-free `S ⊆ ℝ` there is an infinite
`A ⊆ ℕ⁺` such that for every nonempty finite `T ⊆ A` and every `j ∈ {1,…,k}`,
`j · ∑T ∉ S`.  Equivalently `(j · FS(A)) ∩ S = ∅` for all `j ≤ k`.

The k-dependence is explicit and lives entirely in the COLOURING: `n` is coloured by the set
`{ j ∈ {1,…,k} : j·n ∈ S } ⊆ {1,…,k}`, a colouring with at most `2^k` classes.  Sum-freeness of
`S` kills every colour class that contains ANY `j`: if `j·u, j·v ∈ S` for a monochromatic pair
then `j·(u+v) = j·u + j·v ∉ S`, contradicting monochromaticity.  Hence the surviving class is the
empty colour `∅`, on which no `j ≤ k` sends a finite sum into `S`.

Route: Hindman's finite-sums theorem (`Hindman.exists_FS_of_finite_cover`) over `PNat`, the block
machinery of `Erdos949HindmanFS.lean` reproduced verbatim below, and `ypos_finset_sum_mem` to send
an arbitrary finite subset of `A` to a genuine finite sum of the Hindman stream.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Hindman

namespace Erdos949HindmanKfold

/-! ### Block machinery (source-included verbatim from `Erdos949HindmanFS.lean`) -/

/-- `bsum a n` is `a 0 + a 1 + ... + a n`, the sum of the first `n+1` entries of the stream. -/
def bsum : Stream' ℕ+ → ℕ → ℕ+
  | a, 0 => a.head
  | a, (n + 1) => a.head + bsum a.tail n

theorem bsum_zero (a : Stream' ℕ+) : bsum a 0 = a.head := rfl

theorem bsum_succ (a : Stream' ℕ+) (n : ℕ) : bsum a (n + 1) = a.head + bsum a.tail n := rfl

theorem bsum_mem (a : Stream' ℕ+) (n : ℕ) : bsum a n ∈ FS a := by
  induction n generalizing a with
  | zero => exact FS.head a
  | succ n ih =>
      have h := FS.cons a (bsum a.tail n) (ih a.tail)
      rw [bsum_succ]
      exact h

theorem bsum_add_mem (a : Stream' ℕ+) (n : ℕ) (m : ℕ+)
    (hm : m ∈ FS (a.drop (n + 1))) : bsum a n + m ∈ FS a := by
  induction n generalizing a with
  | zero =>
      have hm' : m ∈ FS a.tail := by
        rw [Stream'.tail_eq_drop]
        exact hm
      rw [bsum_zero]
      exact FS.cons a m hm'
  | succ n ih =>
      have hm' : m ∈ FS (a.tail.drop (n + 1)) := by
        rwa [Stream'.drop_succ] at hm
      have h1 : bsum a.tail n + m ∈ FS a.tail := ih a.tail hm'
      have h2 := FS.cons a (bsum a.tail n + m) h1
      rw [bsum_succ, add_assoc]
      exact h2

theorem le_bsum (a : Stream' ℕ+) (n : ℕ) : n + 1 ≤ ((bsum a n : ℕ+) : ℕ) := by
  induction n generalizing a with
  | zero =>
      have h : 1 ≤ ((a.head : ℕ+) : ℕ) := a.head.one_le
      rw [bsum_zero]
      omega
  | succ n ih =>
      have h := ih a.tail
      have hh : 1 ≤ ((a.head : ℕ+) : ℕ) := a.head.one_le
      rw [bsum_succ, PNat.add_coe]
      omega

def blk (a : Stream' ℕ+) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | (k + 1) =>
      ((blk a k).1 + (blk a k).2 + 1, ((bsum (a.drop (blk a k).1) (blk a k).2 : ℕ+) : ℕ))

def ypos (a : Stream' ℕ+) (k : ℕ) : ℕ+ := bsum (a.drop (blk a k).1) (blk a k).2

theorem blk_succ_fst (a : Stream' ℕ+) (k : ℕ) :
    (blk a (k + 1)).1 = (blk a k).1 + (blk a k).2 + 1 := rfl

theorem blk_succ_snd (a : Stream' ℕ+) (k : ℕ) :
    (blk a (k + 1)).2 = ((ypos a k : ℕ+) : ℕ) := rfl

theorem ypos_mem (a : Stream' ℕ+) (k : ℕ) : ypos a k ∈ FS a :=
  FS_iter_tail_sub_FS a (blk a k).1 (bsum_mem (a.drop (blk a k).1) (blk a k).2)

theorem blk_fst_strictMono (a : Stream' ℕ+) : StrictMono (fun k => (blk a k).1) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [blk_succ_fst]
  omega

theorem ypos_strictMono (a : Stream' ℕ+) :
    StrictMono (fun k => ((ypos a k : ℕ+) : ℕ)) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h := le_bsum (a.drop (blk a (k + 1)).1) (blk a (k + 1)).2
  have h2 : (blk a (k + 1)).2 = ((ypos a k : ℕ+) : ℕ) := blk_succ_snd a k
  have h3 : ((ypos a (k + 1) : ℕ+) : ℕ)
      = ((bsum (a.drop (blk a (k + 1)).1) (blk a (k + 1)).2 : ℕ+) : ℕ) := rfl
  omega

theorem FS_drop_mono (a : Stream' ℕ+) {i m : ℕ} (h : i ≤ m) {p : ℕ+}
    (hp : p ∈ FS (a.drop m)) : p ∈ FS (a.drop i) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hd : a.drop (i + d) = (a.drop i).drop d := by
    rw [Stream'.drop_drop]
  rw [hd] at hp
  exact FS_iter_tail_sub_FS (a.drop i) d hp

theorem ypos_finset_sum_mem (a : Stream' ℕ+) :
    ∀ (n : ℕ) (K : Finset ℕ), K.card = n → K.Nonempty → ∀ j : ℕ, (∀ k ∈ K, j ≤ k) →
      ∃ p : ℕ+, p ∈ FS (a.drop (blk a j).1) ∧
        ((p : ℕ+) : ℕ) = ∑ k ∈ K, ((ypos a k : ℕ+) : ℕ) := by
  intro n
  induction n with
  | zero =>
      intro K hcard hK _ _
      rw [Finset.card_eq_zero] at hcard
      subst hcard
      exact absurd hK (by simp)
  | succ n ih =>
      intro K hcard hK j hj
      have hmin0 : K.min' hK ∈ K := K.min'_mem hK
      obtain ⟨j', hj'K, hmin⟩ : ∃ j' ∈ K, ∀ k ∈ K, j' ≤ k :=
        ⟨K.min' hK, hmin0, fun k hk => K.min'_le k hk⟩
      have hjj' : j ≤ j' := hj j' hj'K
      have hstart : (blk a j).1 ≤ (blk a j').1 := (blk_fst_strictMono a).monotone hjj'
      have hcard' : (K.erase j').card = n := by
        rw [Finset.card_erase_of_mem hj'K, hcard]
        rfl
      have hsplit : ∑ k ∈ K, ((ypos a k : ℕ+) : ℕ)
          = ((ypos a j' : ℕ+) : ℕ) + ∑ k ∈ K.erase j', ((ypos a k : ℕ+) : ℕ) :=
        (Finset.add_sum_erase K (fun k => ((ypos a k : ℕ+) : ℕ)) hj'K).symm
      have hyp : ypos a j' = bsum (a.drop (blk a j').1) (blk a j').2 := rfl
      rcases Finset.eq_empty_or_nonempty (K.erase j') with hE | hNE
      · refine ⟨ypos a j', ?_, ?_⟩
        · refine FS_drop_mono a hstart ?_
          rw [hyp]
          exact bsum_mem (a.drop (blk a j').1) (blk a j').2
        · rw [hsplit, hE, Finset.sum_empty, Nat.add_zero]
      · have hgt : ∀ k ∈ K.erase j', j' + 1 ≤ k := by
          intro k hk
          have hkK : k ∈ K := Finset.mem_of_mem_erase hk
          have hne : k ≠ j' := Finset.ne_of_mem_erase hk
          have hle := hmin k hkK
          omega
        obtain ⟨q, hq, hqval⟩ := ih (K.erase j') hcard' hNE (j' + 1) hgt
        have hstep : (blk a (j' + 1)).1 = (blk a j').1 + ((blk a j').2 + 1) := by
          rw [blk_succ_fst]
          omega
        have hq2 : q ∈ FS ((a.drop (blk a j').1).drop ((blk a j').2 + 1)) := by
          rw [Stream'.drop_drop, ← hstep]
          exact hq
        have hp := bsum_add_mem (a.drop (blk a j').1) (blk a j').2 q hq2
        refine ⟨ypos a j' + q, ?_, ?_⟩
        · refine FS_drop_mono a hstart ?_
          rw [hyp]
          exact hp
        · rw [hsplit, PNat.add_coe, hqval]

/-! ### The k-fold promoted theorem -/

/-- **Erdős 949, countable analogue, k-FOLD FINITE-SUMS FORM.**
For every fixed `k` and every sum-free `S ⊆ ℝ` there is an infinite set `A` of positive naturals
such that for every nonempty finite `T ⊆ A` and every `j` with `1 ≤ j ≤ k`, the scaled finite sum
`j · ∑T` lies outside `S`.  The sealed `erdos949_hindman_full_finite_sums` is the `k = 2` case. -/
theorem erdos949_hindman_kfold (k : ℕ) (S : Set ℝ)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
      ∀ T : Finset ℕ, T.Nonempty → (↑T : Set ℕ) ⊆ A →
        ∀ j : ℕ, 1 ≤ j → j ≤ k → ((j * (∑ n ∈ T, n) : ℕ) : ℝ) ∉ S := by
  classical
  -- colour `n` by the subset of `{1,…,k}` of multipliers that land in `S`
  let col : ℕ+ → Finset ℕ := fun n => (Finset.Icc 1 k).filter (fun i => ((i * (n : ℕ) : ℕ) : ℝ) ∈ S)
  have hcol_mem : ∀ (n : ℕ+) (i : ℕ), i ∈ col n ↔ (1 ≤ i ∧ i ≤ k ∧ ((i * (n : ℕ) : ℕ) : ℝ) ∈ S) := by
    intro n i
    constructor
    · intro h
      have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp h).1
      exact ⟨h1.1, h1.2, (Finset.mem_filter.mp h).2⟩
    · rintro ⟨hi1, hik, hiS⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi1, hik⟩, hiS⟩
  have hcol_sub : ∀ n : ℕ+, col n ∈ (Finset.Icc 1 k).powerset :=
    fun n => Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  set cover : Set (Set ℕ+) :=
    (fun c => {n : ℕ+ | col n = c}) '' ((Finset.Icc 1 k).powerset : Set (Finset ℕ)) with hcover
  have hfin : cover.Finite := by
    rw [hcover]
    exact Set.Finite.image _ ((Finset.Icc 1 k).powerset).finite_toSet
  have hcov : (⊤ : Set ℕ+) ⊆ ⋃₀ cover := by
    intro n _
    refine ⟨{m : ℕ+ | col m = col n}, ?_, rfl⟩
    rw [hcover]
    exact ⟨col n, Finset.mem_coe.mpr (hcol_sub n), rfl⟩
  obtain ⟨c, hcmem, a, hFS⟩ := Hindman.exists_FS_of_finite_cover cover hfin hcov
  rw [hcover, Set.mem_image] at hcmem
  obtain ⟨d, -, hd_eq⟩ := hcmem
  -- every finite-sum element carries colour `d`
  have hcolFS : ∀ {m : ℕ+}, m ∈ FS a → col m = d := by
    intro m hm
    have hmc : m ∈ c := hFS hm
    rw [← hd_eq] at hmc
    exact hmc
  -- `ypos a 0 + ypos a 1` is a genuine finite sum of the stream
  have hpair : ypos a 0 + ypos a 1 ∈ FS a := by
    obtain ⟨p, hp, hpval⟩ :=
      ypos_finset_sum_mem a ({0, 1} : Finset ℕ).card ({0, 1} : Finset ℕ) rfl ⟨0, by simp⟩ 0
        (fun k _ => Nat.zero_le k)
    have hpa : p ∈ FS a := FS_iter_tail_sub_FS a (blk a 0).1 hp
    have hsum : ∑ i ∈ ({0, 1} : Finset ℕ), ((ypos a i : ℕ+) : ℕ)
        = ((ypos a 0 : ℕ+) : ℕ) + ((ypos a 1 : ℕ+) : ℕ) := by
      rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    have hpe : p = ypos a 0 + ypos a 1 := by
      have : ((p : ℕ+) : ℕ) = (((ypos a 0 + ypos a 1 : ℕ+) : ℕ)) := by
        rw [hpval, hsum, PNat.add_coe]
      exact PNat.coe_injective this
    rwa [hpe] at hpa
  -- the surviving colour is empty: no multiplier `j ≤ k` sends the mono class into `S`
  have hdempty : d = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨j, hj⟩
    have hu : j ∈ col (ypos a 0) := by rw [hcolFS (ypos_mem a 0)]; exact hj
    have hv : j ∈ col (ypos a 1) := by rw [hcolFS (ypos_mem a 1)]; exact hj
    have huv : j ∈ col (ypos a 0 + ypos a 1) := by rw [hcolFS hpair]; exact hj
    have hju := (hcol_mem (ypos a 0) j).mp hu
    have hjv := (hcol_mem (ypos a 1) j).mp hv
    have hjuv := (hcol_mem (ypos a 0 + ypos a 1) j).mp huv
    have hkey : ((j * ((ypos a 0 : ℕ+) : ℕ) : ℕ) : ℝ) + ((j * ((ypos a 1 : ℕ+) : ℕ) : ℕ) : ℝ) ∈ S := by
      have hcast : ((j * (((ypos a 0 + ypos a 1 : ℕ+) : ℕ)) : ℕ) : ℝ)
          = ((j * ((ypos a 0 : ℕ+) : ℕ) : ℕ) : ℝ) + ((j * ((ypos a 1 : ℕ+) : ℕ) : ℕ) : ℝ) := by
        rw [PNat.add_coe]; push_cast; ring
      have := hjuv.2.2
      rwa [hcast] at this
    exact hS _ hju.2.2 _ hjv.2.2 hkey
  -- assemble the witness
  set f : ℕ → ℕ := fun k => ((ypos a k : ℕ+) : ℕ) with hf
  have hinj : Function.Injective f := (ypos_strictMono a).injective
  refine ⟨Set.range f, Set.infinite_range_of_injective hinj, ?_, ?_⟩
  · rintro n ⟨k, rfl⟩
    exact (ypos a k).pos
  · intro T hT hTA j hj1 hjk
    set K : Finset ℕ := T.preimage f hinj.injOn with hK
    have hmemK : ∀ x : ℕ, x ∈ K ↔ f x ∈ T := by
      intro x; rw [hK, Finset.mem_preimage]
    have himg : K.image f = T := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (hmemK w).mp hw
      · intro hx
        obtain ⟨w, hw⟩ := hTA (Finset.mem_coe.mpr hx)
        exact ⟨w, (hmemK w).mpr (by rw [hw]; exact hx), hw⟩
    have hKne : K.Nonempty := by
      obtain ⟨x, hx⟩ := hT
      obtain ⟨w, hw⟩ := hTA (Finset.mem_coe.mpr hx)
      exact ⟨w, (hmemK w).mpr (by rw [hw]; exact hx)⟩
    have hsumT : ∑ n ∈ T, n = ∑ x ∈ K, f x := by
      rw [← himg, Finset.sum_image (fun x _ y _ h => hinj h)]
    obtain ⟨p, hp, hpval⟩ :=
      ypos_finset_sum_mem a K.card K rfl hKne 0 (fun x _ => Nat.zero_le x)
    have hpa : p ∈ FS a := FS_iter_tail_sub_FS a (blk a 0).1 hp
    have hcolp : col p = ∅ := by rw [hcolFS hpa]; exact hdempty
    have hval : ((p : ℕ+) : ℕ) = ∑ n ∈ T, n := by rw [hpval, hsumT]
    intro hmem
    have hjcol : j ∈ col p := by
      rw [hcol_mem]
      refine ⟨hj1, hjk, ?_⟩
      rw [hval]
      exact hmem
    rw [hcolp] at hjcol
    exact absurd hjcol (Finset.notMem_empty j)

/-! ### The sealed `k = 2` statement, recovered as a corollary -/

/-- **Erdős 949, full finite-sums form** (the statement sealed in `Erdos949HindmanFS.lean`),
recovered as the `k = 2` case of `erdos949_hindman_kfold`.  This exhibits the k-fold theorem as a
strict generalisation of the sealed result. -/
theorem erdos949_hindman_full_finite_sums (S : Set ℝ)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
      ∀ T : Finset ℕ, T.Nonempty → (↑T : Set ℕ) ⊆ A →
        ((((∑ n ∈ T, n : ℕ)) : ℝ) ∉ S ∧ ((2 * (∑ n ∈ T, n) : ℕ) : ℝ) ∉ S) := by
  obtain ⟨A, hinf, hpos, hk⟩ := erdos949_hindman_kfold 2 S hS
  refine ⟨A, hinf, hpos, ?_⟩
  intro T hT hTA
  refine ⟨?_, hk T hT hTA 2 (by norm_num) (by norm_num)⟩
  have h1 := hk T hT hTA 1 (by norm_num) (by norm_num)
  simpa using h1

/-! ### Non-vacuity control -/

/-- Known-answer control: the k-fold conclusion is unsatisfiable for `S = univ` (not sum-free),
so the theorem is not vacuous and the sum-free hypothesis is load-bearing.  Stated for `k = 1`
(already the `j = 1` shadow rules `A` out). -/
theorem erdos949_hindman_kfold_control :
    ¬ ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
      ∀ T : Finset ℕ, T.Nonempty → (↑T : Set ℕ) ⊆ A →
        ∀ j : ℕ, 1 ≤ j → j ≤ 1 → ((j * (∑ n ∈ T, n) : ℕ) : ℝ) ∉ (Set.univ : Set ℝ) := by
  rintro ⟨A, hA, -, h⟩
  obtain ⟨n, hn⟩ := hA.nonempty
  have hsub : (↑({n} : Finset ℕ) : Set ℕ) ⊆ A := by
    simp only [Finset.coe_singleton, Set.singleton_subset_iff]
    exact hn
  exact h {n} (Finset.singleton_nonempty n) hsub 1 (by norm_num) (by norm_num) (Set.mem_univ _)

end Erdos949HindmanKfold

#print axioms Erdos949HindmanKfold.ypos_finset_sum_mem
#print axioms Erdos949HindmanKfold.erdos949_hindman_kfold
#print axioms Erdos949HindmanKfold.erdos949_hindman_full_finite_sums
#print axioms Erdos949HindmanKfold.erdos949_hindman_kfold_control
