/-
  Erdős Problem 40 — kernel-checked structural core.

  Target (OPEN, $500, erdosproblems.com/40, read 2026-09-05):

      For what functions `g(N) → ∞` is it true that
          |A ∩ {1,…,N}| ≫ N^{1/2} / g(N)
      implies `limsup 1_A ∗ 1_A(n) = ∞`?

  THIS FILE DOES NOT CLOSE THAT PROBLEM.  It proves, sorry-free:
    * a semantic binding of `rep` to the upstream `sumRep` and of `cnt` to the upstream
      `(A ∩ Set.Icc 1 N).ncard`;
    * that the answer set is DOWNWARD CLOSED in the growth order on `g`;
    * a REFUTATION CRITERION: one set with a bounded representation function and large
      enough counting function knocks `g` out of the answer set;
    * an exact REFORMULATION of `Erdos40For g` as a statement purely about sets with a
      bounded representation function.

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Mathlib

namespace Erdos40

open Finset Filter Set Asymptotics
open scoped Topology

attribute [local instance 100] Classical.propDecidable

/-- `rep A n` is the number of ORDERED pairs `(a, b) ∈ A × A` with `a + b = n`.
This is `(1_A ∗ 1_A) n`; see `rep_eq_sumConv` for the binding to the upstream `sumRep`. -/
noncomputable def rep (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card

/-- `cnt A N = |A ∩ {1, …, N}|`.  See `ncard_eq_cnt` for the binding to the upstream
`(A ∩ Set.Icc 1 N).ncard`. -/
noncomputable def cnt (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun a => a ∈ A)).card

/-- **The formalised statement of Erdős 40 for a single `g`.**  Verbatim the upstream
`Erdos40.Erdos40For` of google-deepmind/formal-conjectures, with `sumRep` replaced by the
definitionally-bound `rep` (see `rep_eq_sumConv`). -/
def Erdos40For (g : ℕ → ℝ) : Prop :=
  ∀ A : Set ℕ,
    (fun N : ℕ => Real.sqrt (N : ℝ) / g N) =O[atTop]
      (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ)) →
    limsup (fun N : ℕ => (rep A N : ℕ∞)) atTop = ⊤

/-! ## Semantic bindings to the upstream statement -/

/-- **Binding lemma (representation function).**  `rep` is literally the upstream
`sumRep A n = (𝟙_A ∗ 𝟙_A) n = ∑ p ∈ antidiagonal n, 1_A p.1 * 1_A p.2`. -/
theorem rep_eq_sumConv (A : Set ℕ) (n : ℕ) :
    rep A n = ∑ p ∈ Finset.antidiagonal n,
      (Set.indicator A (fun _ => (1 : ℕ)) p.1) * (Set.indicator A (fun _ => (1 : ℕ)) p.2) := by
  rw [rep, Finset.card_filter]
  refine Finset.sum_congr rfl ?_
  intro p _
  by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ A <;> simp [h1, h2]

/-- **Binding lemma (counting function).**  `cnt A N` is the upstream
`(A ∩ Set.Icc 1 N).ncard`. -/
theorem ncard_eq_cnt (A : Set ℕ) (N : ℕ) : (A ∩ Set.Icc 1 N).ncard = cnt A N := by
  have h : A ∩ Set.Icc 1 N = ↑((Finset.Icc 1 N).filter (fun a => a ∈ A)) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_Icc]
    tauto
  rw [h, Set.ncard_coe_finset, cnt]

/-! ## `limsup = ⊤` versus boundedness of `rep` -/

/-- `r_A(n) ≤ n + 1` always: the antidiagonal of `n` has `n + 1` elements. -/
theorem rep_le_succ (A : Set ℕ) (n : ℕ) : rep A n ≤ n + 1 := by
  have h : ((Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card
      ≤ (Finset.range (n + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal] at hp
      simp only [Finset.mem_coe, Finset.mem_range]
      omega
    · intro p hp q hq hpq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal] at hp hq
      obtain ⟨p1, p2⟩ := p
      obtain ⟨q1, q2⟩ := q
      dsimp only at hp hq hpq
      subst hpq
      simp only [Prod.mk.injEq, true_and]
      omega
  simpa [rep] using h

/-- If `r_A` is bounded by `B` then the `limsup` is at most `B`, in particular `≠ ⊤`. -/
theorem limsup_le_of_rep_le {A : Set ℕ} {B : ℕ} (h : ∀ n, rep A n ≤ B) :
    limsup (fun N : ℕ => (rep A N : ℕ∞)) atTop ≤ (B : ℕ∞) := by
  refine limsup_le_of_le isCobounded_le_of_bot ?_
  exact Eventually.of_forall (fun n => by exact_mod_cast h n)

/-- Conversely, `limsup ≠ ⊤` forces `r_A` to be bounded (uniformly, on all of `ℕ`). -/
theorem rep_bdd_of_limsup_ne_top {A : Set ℕ}
    (h : limsup (fun N : ℕ => (rep A N : ℕ∞)) atTop ≠ ⊤) :
    ∃ B : ℕ, ∀ n, rep A n ≤ B := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
  have hlt : limsup (fun N : ℕ => (rep A N : ℕ∞)) atTop < ((m + 1 : ℕ) : ℕ∞) := by
    rw [← hm]
    exact_mod_cast Nat.lt_succ_self m
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (Filter.eventually_lt_of_limsup_lt hlt)
  refine ⟨max m (n₀ + 1), fun n => ?_⟩
  by_cases hn : n₀ ≤ n
  · have h1 : (rep A n : ℕ∞) < ((m + 1 : ℕ) : ℕ∞) := hn₀ n hn
    have h2 : rep A n < m + 1 := by exact_mod_cast h1
    omega
  · have := rep_le_succ A n
    omega

/-- `limsup = ⊤` is exactly unboundedness of `r_A`. -/
theorem limsup_eq_top_iff (A : Set ℕ) :
    limsup (fun N : ℕ => (rep A N : ℕ∞)) atTop = ⊤ ↔ ¬ ∃ B : ℕ, ∀ n, rep A n ≤ B := by
  constructor
  · intro htop ⟨B, hB⟩
    have hle := limsup_le_of_rep_le hB
    rw [htop, top_le_iff] at hle
    exact absurd hle (by simp)
  · intro hnb
    by_contra hne
    exact hnb (rep_bdd_of_limsup_ne_top hne)

/-! ## The refutation criterion -/

/-- **Refutation criterion.**  A single set `A` whose representation function is bounded and
whose counting function dominates the threshold `√N / g N` knocks `g` out of the answer set
of Erdős 40. -/
theorem not_erdos40For_of_bounded_witness {g : ℕ → ℝ} {A : Set ℕ} {B : ℕ}
    (hbdd : ∀ n, rep A n ≤ B)
    (hdens : (fun N : ℕ => Real.sqrt (N : ℝ) / g N) =O[atTop]
      (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ))) :
    ¬ Erdos40For g := by
  intro H
  have htop := H A hdens
  have hle := limsup_le_of_rep_le hbdd
  rw [htop, top_le_iff] at hle
  exact absurd hle (by simp)

/-- **Reformulation.**  `Erdos40For g` says exactly: every set with a bounded representation
function has counting function `o`-failing the threshold `√N / g(N)`.  This is the form in
which Erdős 40 meets the question of how dense an infinite Sidon (or `B₂[k]`) set can be. -/
theorem erdos40For_iff (g : ℕ → ℝ) :
    Erdos40For g ↔
      ∀ A : Set ℕ, (∃ B : ℕ, ∀ n, rep A n ≤ B) →
        ¬ ((fun N : ℕ => Real.sqrt (N : ℝ) / g N) =O[atTop]
            (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ))) := by
  constructor
  · rintro H A ⟨B, hB⟩ hdens
    exact not_erdos40For_of_bounded_witness hB hdens H
  · intro H A hdens
    by_contra hne
    exact H A (rep_bdd_of_limsup_ne_top hne) hdens

/-! ## The answer set is downward closed -/

/-- **Monotonicity (`=O` form).**  If the `g₂`-threshold is dominated by the `g₁`-threshold,
then `Erdos40For g₂` is the stronger statement. -/
theorem Erdos40For.of_isBigO {g₁ g₂ : ℕ → ℝ}
    (h : (fun N : ℕ => Real.sqrt (N : ℝ) / g₂ N) =O[atTop]
         (fun N : ℕ => Real.sqrt (N : ℝ) / g₁ N))
    (H : Erdos40For g₂) : Erdos40For g₁ :=
  fun A hA => H A (h.trans hA)

/-- **Monotonicity (pointwise form).**  The answer set of Erdős 40 is DOWNWARD CLOSED: if
`g₁ ≤ g₂` eventually and `g₁ > 0` eventually, then `g₂` being an answer forces `g₁` to be one. -/
theorem Erdos40For.of_le {g₁ g₂ : ℕ → ℝ}
    (hpos : ∀ᶠ N : ℕ in atTop, 0 < g₁ N) (hle : ∀ᶠ N : ℕ in atTop, g₁ N ≤ g₂ N)
    (H : Erdos40For g₂) : Erdos40For g₁ := by
  refine Erdos40For.of_isBigO ?_ H
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hpos, hle] with N h1 h2
  have hs : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have h2' : (0 : ℝ) < g₂ N := lt_of_lt_of_le h1 h2
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hs h2'.le), abs_of_nonneg (div_nonneg hs h1.le)]
  gcongr

end Erdos40
