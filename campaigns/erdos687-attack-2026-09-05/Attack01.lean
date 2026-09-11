/-
# Erdős #687 — attack (2026-09-05), sub-openA

Target row: erdos:687 ($1000). Targets = {Question, QuestionSharp,
MaierPomeranceConjecture, QuestionWeakVariant}. All four are the genuinely OPEN
asymptotic questions; none is closable here and none is weakened below.

This file:
  * reproduces the spec defs VERBATIM (Covers, CoverSet, Y, Question, QuestionSharp,
    MaierPomeranceConjecture, uncoveredCount, AlmostCovers, QuestionWeakVariant);
  * SEALS `questionSharp_imp_question` (stated `sorry` in the frozen spec, NOT a target):
    the sharp form x^{1+o(1)} implies the o(x^2) form — pure asymptotics;
  * records a typed OBSTRUCTION / FINDING: the shape of the best-known bound (Iwaniec,
    Y ≪ x^2) does NOT imply `Question` (Y = o(x^2)); the gap is real, so the known
    bound alone cannot close #687.

Clean footprint target: [propext, Classical.choice, Quot.sound]. sorryAx = NOT proved.
-/
import Mathlib
namespace Erdos687

open Filter

/-! ### Defs — VERBATIM from oracle/evidence/formalizer-sources/erdos/erdos-687.lean -/

def Covers (x y : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ n ∈ Finset.Icc 1 y, ∃ p ∈ Nat.primesLE x, n ≡ a p [MOD p]

def CoverSet (x : ℕ) : Set ℕ := {y | Covers x y}

noncomputable def Y (x : ℕ) : ℕ := sSup (CoverSet x)

/-! ### Two proved controls, VERBATIM (compile sanity) -/

theorem covers_zero (x : ℕ) : Covers x 0 := by
  refine ⟨fun _ => 0, ?_⟩
  intro n hn
  rw [Finset.mem_Icc] at hn
  exact absurd hn (by omega)

theorem coverSet_nonempty (x : ℕ) : (CoverSet x).Nonempty :=
  ⟨0, covers_zero x⟩

/-! ### THE QUESTION — targets, VERBATIM, NOT asserted -/

def Question : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, (Y x : ℝ) ≤ ε * (x : ℝ) ^ 2

def QuestionSharp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
    (Y x : ℝ) ≤ C * (x : ℝ) ^ ((1 : ℝ) + ε)

def MaierPomeranceConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
    (Y x : ℝ) ≤ C * (x : ℝ) * (Real.log x) ^ ((2 : ℝ) + ε)

noncomputable def uncoveredCount (x y : ℕ) (a : ℕ → ℕ) : ℕ :=
  {n : ℕ | 1 ≤ n ∧ n ≤ y ∧ ∀ p ∈ Nat.primesLE x, ¬ n ≡ a p [MOD p]}.ncard

def AlmostCovers (x y : ℕ) (c : ℝ) : Prop :=
  ∃ a : ℕ → ℕ, (uncoveredCount x y a : ℝ) ≤ c * (y : ℝ) / Real.log y

def QuestionWeakVariant : Prop :=
  ∀ c : ℝ, 0 < c → ∀ K : ℝ, ∀ᶠ x : ℕ in atTop,
    ∃ y : ℕ, K * (Y x : ℝ) ≤ (y : ℝ) ∧ AlmostCovers x y c

/-! ### SEAL — a stated `sorry` from the spec (NOT a target): sharp ⇒ o(x²). -/

/-- **SEALED.**  `QuestionSharp → Question`.  Take the sharp bound at exponent `1/2`
(`Y x ≤ C·x^{3/2}`); since `C·x^{3/2} ≤ ε·x²` once `x^{1/2} ≥ C/ε`, the `o(x²)` bound
follows.  Pure asymptotics; independent of the (open) truth of either side. -/
theorem questionSharp_imp_question : QuestionSharp → Question := by
  intro hs ε hε
  obtain ⟨C, hC, hev⟩ := hs (1 / 2) (by norm_num)
  have hrp : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun n : ℕ => ε * (n : ℝ) ^ ((1 : ℝ) / 2)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hε hrp
  have hge : ∀ᶠ x : ℕ in atTop, C ≤ ε * (x : ℝ) ^ ((1 : ℝ) / 2) :=
    htend.eventually_ge_atTop C
  filter_upwards [hev, hge, eventually_gt_atTop 0] with x hx hxge hxpos
  have hxr : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxpos
  have e1 : (x : ℝ) ^ ((1 : ℝ) + 1 / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_add hxr]
    rw [show (1 : ℝ) + 1 / 2 + 1 / 2 = ((2 : ℕ) : ℝ) by norm_num]
    rw [Real.rpow_natCast]
  have hpow_nonneg : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) + 1 / 2) := Real.rpow_nonneg (le_of_lt hxr) _
  calc (Y x : ℝ) ≤ C * (x : ℝ) ^ ((1 : ℝ) + 1 / 2) := hx
    _ ≤ (ε * (x : ℝ) ^ ((1 : ℝ) / 2)) * (x : ℝ) ^ ((1 : ℝ) + 1 / 2) :=
        mul_le_mul_of_nonneg_right hxge hpow_nonneg
    _ = ε * (x : ℝ) ^ (2 : ℕ) := by rw [← e1]; ring

/-- **SEALED.**  `MaierPomeranceConjecture → Question`.  Take the conjecture at exponent
`ε' = 1` (`Y x ≤ C·x·(log x)^3`).  Since `(log x)^3 = o(x)` (`isLittleO_log_rpow_rpow_atTop`),
eventually `C·x·(log x)^3 ≤ ε·x²`.  Pure asymptotics; independent of the (open) conjecture. -/
theorem maierPomerance_imp_question : MaierPomeranceConjecture → Question := by
  intro hmp ε hε
  obtain ⟨C, hC, hev⟩ := hmp 1 (by norm_num)
  have hCne : C ≠ 0 := ne_of_gt hC
  have hlo : (fun x : ℝ => (Real.log x) ^ ((2 : ℝ) + 1)) =o[atTop] (fun x : ℝ => x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop ((2 : ℝ) + 1) (by norm_num)
  have hloN : (fun n : ℕ => (Real.log n) ^ ((2 : ℝ) + 1)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) :=
    hlo.comp_tendsto tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖(Real.log n) ^ ((2 : ℝ) + 1)‖ ≤ (ε / C) * ‖(n : ℝ) ^ (1 : ℝ)‖ :=
    Asymptotics.isLittleO_iff.mp hloN (by positivity)
  filter_upwards [hev, hbound, eventually_gt_atTop 1] with x hx hb hx1
  have hx0 : (0 : ℝ) < (x : ℝ) := by positivity
  have hxr : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  have hlog : 0 < Real.log x := Real.log_pos hxr
  have hlogr : (0 : ℝ) < (Real.log x) ^ ((2 : ℝ) + 1) := Real.rpow_pos_of_pos hlog _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one, abs_of_pos hlogr, abs_of_pos hx0] at hb
  have hCx : (0 : ℝ) ≤ C * (x : ℝ) := by positivity
  calc (Y x : ℝ) ≤ C * (x : ℝ) * (Real.log x) ^ ((2 : ℝ) + 1) := hx
    _ ≤ C * (x : ℝ) * ((ε / C) * (x : ℝ)) := mul_le_mul_of_nonneg_left hb hCx
    _ = ε * (x : ℝ) ^ 2 := by field_simp

/-! ### FINDING — typed obstruction: the known bound's SHAPE cannot close #687. -/

/-- **FINDING (typed obstruction).**  Iwaniec's best-known bound is `Y(x) ≪ x²`, i.e. the
shape `∃ C > 0, ∀ᶠ x, f x ≤ C·x²`.  `Question` asks for `Y(x) = o(x²)`, the shape
`∀ ε > 0, ∀ᶠ x, f x ≤ ε·x²`.  These are inequivalent for a nonnegative function: `f = x²`
satisfies the former (C = 1) yet refutes the latter (ε = 1/2).  Hence no rearrangement of
the known bound alone settles #687 — the open gap between `≪ x²` and `o(x²)` is genuine. -/
theorem bigO_sq_not_imp_littleO_sq :
    ∃ f : ℕ → ℝ, (∀ n, 0 ≤ f n) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, f n ≤ C * (n : ℝ) ^ 2) ∧
      ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ ε * (n : ℝ) ^ 2) := by
  refine ⟨fun n => (n : ℝ) ^ 2, fun n => by positivity, ⟨1, one_pos, ?_⟩, ?_⟩
  · filter_upwards with n; simp
  · intro h
    have h2 := h (1 / 2) (by norm_num)
    rw [eventually_atTop] at h2
    obtain ⟨N, hN⟩ := h2
    have hbig := hN (N + 1) (by omega)
    simp only [] at hbig
    have hpos : (0 : ℝ) < ((N : ℝ) + 1) ^ 2 := by positivity
    push_cast at hbig
    nlinarith [hbig, hpos]

end Erdos687

-- ⛔ FOOTPRINTS
#print axioms Erdos687.covers_zero
#print axioms Erdos687.coverSet_nonempty
#print axioms Erdos687.questionSharp_imp_question
#print axioms Erdos687.maierPomerance_imp_question
#print axioms Erdos687.bigO_sq_not_imp_littleO_sq
