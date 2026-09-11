/-
  Erdős Problem 28 — the Erdős–Turán conjecture on additive bases.
  Kernel-checked structural core.

  Target (OPEN, $500, erdosproblems.com/28):
      If `A ⊆ ℕ` is such that `A + A` contains all but finitely many integers
      (an additive basis of order 2), must `limsup (1_A ∗ 1_A)(n) = ∞`?

  Formalised upstream at
  `google-deepmind/formal-conjectures : FormalConjectures/ErdosProblems/28.lean`
  as

      @[category research open, AMS 11]
      theorem erdos_28 (A : Set ℕ) (h : (A + A)ᶜ.Finite) :
          limsup (fun (n : ℕ) => (sumRep A n : ℕ∞)) atTop = (⊤ : ℕ∞) := by sorry

  THIS FILE DOES NOT CLOSE THAT PROBLEM.  It proves, sorry-free, the semantic binding of
  the object studied here to the upstream `sumRep`, and the exact translation of the
  `limsup = ⊤` conclusion into uniform boundedness of the representation function.

  Reused, with credit, from the sibling campaigns in this estate (both kernel-checked
  under the same toolchain):
    * `erdos40-close-2026-09-05/lean/Erdos40Core.lean`  — `rep`, `rep_eq_sumConv`,
      `rep_le_succ`, `limsup_le_of_rep_le`, `rep_bdd_of_limsup_ne_top`, `limsup_eq_top_iff`.
    * `erdos66-close-2026-09-05/lean/Erdos66Core.lean`  — the `cnt`/`pairsLe` conventions.

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Mathlib

namespace Erdos28

open Finset Filter Set
open scoped Topology Pointwise

attribute [local instance 100] Classical.propDecidable

/-- `rep A n` is the number of ORDERED pairs `(a, b) ∈ A × A` with `a + b = n`.
This is `(1_A ∗ 1_A) n`; see `rep_eq_sumConv` for the binding to the upstream `sumRep`. -/
noncomputable def rep (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card

/-- `cnt A N = |A ∩ [0, N]|`.  The window INCLUDES `0`; see `Erdos40.cnt_zero_le` in the
sibling campaign for the comparison with the `[1,N]` convention. -/
noncomputable def cnt (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun a => a ∈ A)).card

/-- `IsBasis2 A` is verbatim the upstream hypothesis of `erdos_28`: `A + A` omits only
finitely many naturals. -/
def IsBasis2 (A : Set ℕ) : Prop := (A + A)ᶜ.Finite

/-- **The formalised statement of Erdős 28**, verbatim the upstream `erdos_28` with
`sumRep` replaced by the definitionally-bound `rep` (see `rep_eq_sumConv`). -/
def Erdos28Stmt : Prop :=
  ∀ A : Set ℕ, IsBasis2 A → limsup (fun n : ℕ => (rep A n : ℕ∞)) atTop = (⊤ : ℕ∞)

/-! ## Semantic binding to the upstream statement -/

/-- **Binding lemma.**  `rep` is literally the upstream
`sumRep A n = (𝟙_A ∗ 𝟙_A) n = ∑ p ∈ antidiagonal n, 1_A p.1 * 1_A p.2`.
This is the guard against a formal/prose mismatch: everything below is a statement about
the object named in the formalised Erdős 28. -/
theorem rep_eq_sumConv (A : Set ℕ) (n : ℕ) :
    rep A n = ∑ p ∈ Finset.antidiagonal n,
      (Set.indicator A (fun _ => (1 : ℕ)) p.1) * (Set.indicator A (fun _ => (1 : ℕ)) p.2) := by
  rw [rep, Finset.card_filter]
  refine Finset.sum_congr rfl ?_
  intro p _
  by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ A <;> simp [h1, h2]

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

/-- Conversely, `limsup ≠ ⊤` forces `r_A` to be bounded UNIFORMLY on all of `ℕ`, not merely
eventually. -/
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

/-- **`limsup = ⊤` is exactly unboundedness of `r_A`.**  This is the exact translation of the
Erdős 28 conclusion into elementary language. -/
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

/-- **The exact contrapositive shape of a counterexample.**  Erdős 28 fails iff some additive
basis of order 2 is a `B₂[B]` set: its representation function is bounded by a single `B`,
uniformly on all of `ℕ`. -/
theorem erdos28_iff_no_bounded_basis :
    Erdos28Stmt ↔ ¬ ∃ (A : Set ℕ) (B : ℕ), IsBasis2 A ∧ ∀ n, rep A n ≤ B := by
  constructor
  · rintro H ⟨A, B, hA, hB⟩
    have htop := H A hA
    have hle := limsup_le_of_rep_le hB
    rw [htop, top_le_iff] at hle
    exact absurd hle (by simp)
  · intro H A hA
    rw [limsup_eq_top_iff]
    rintro ⟨B, hB⟩
    exact H ⟨A, B, hA, hB⟩

/-! ## The basis hypothesis is a representation lower bound -/

/-- A basis of order 2 has `r_A(n) ≥ 1` for every large `n`.  This unpacks `(A + A)ᶜ.Finite`
into the pointwise statement the counting arguments consume. -/
theorem one_le_rep_of_basis {A : Set ℕ} (hA : IsBasis2 A) :
    ∃ M : ℕ, ∀ n : ℕ, M < n → 1 ≤ rep A n := by
  classical
  obtain ⟨M, hM⟩ := hA.bddAbove
  refine ⟨M, fun n hn => ?_⟩
  have hnot : n ∉ (A + A)ᶜ := by
    intro hmem
    have := hM hmem
    omega
  have hmem : n ∈ A + A := by
    by_contra hcon
    exact hnot hcon
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have hab' : a + b = n := hab
  have : (a, b) ∈ (Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A) :=
    Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr hab', ha, hb⟩
  exact Finset.card_pos.mpr ⟨(a, b), this⟩

end Erdos28
