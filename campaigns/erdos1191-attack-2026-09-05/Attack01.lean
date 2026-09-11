/-
# Erdős problem 1191 — ATTACK 01 (2026-09-05)

Self-contained. Definitions `IsSidon`, `countSet`, `countUpTo`, `sidonWeight`, `Question1`,
`Question2`, `Question2'`, and the control `finite_countSet` are COPIED VERBATIM from
`oracle/evidence/formalizer-sources/erdos/erdos-1191.lean`. That spec file is NOT modified and
is NOT imported (it is a standalone artifact); copying keeps the statements literally identical.

NOTHING here asserts an answer to `Question1` or `Question2`. Everything below is either a
proved lemma or a proved CONDITIONAL whose hypothesis is displayed in its own statement.
-/
import Mathlib
open Filter Finset

namespace Erdos1191

/-! ## VERBATIM COPIES from the frozen spec -/

def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def countSet (A : Set ℕ) (x : ℝ) : Set ℕ := {n | n ∈ A ∧ 1 ≤ n ∧ (n : ℝ) ≤ x}

noncomputable def countUpTo (A : Set ℕ) (x : ℝ) : ℕ := (countSet A x).ncard

noncomputable def sidonWeight (A : Set ℕ) (c : ℝ) (x : ℝ) : ℝ :=
  (countUpTo A x : ℝ) / Real.sqrt x * Real.log x ^ c

def Question1 : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsSidon A → liminf (sidonWeight A (1 / 2)) atTop = 0

def Question2 : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ ∃ c : ℝ, 0 < c ∧ 0 < liminf (sidonWeight A c) atTop

def Question2' : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
    ∀ᶠ x in (atTop : Filter ℝ), ε ≤ sidonWeight A c x

theorem finite_countSet (A : Set ℕ) (x : ℝ) : (countSet A x).Finite := by
  apply Set.Finite.subset (Set.finite_Icc 1 ⌊x⌋₊)
  rintro n ⟨-, h1, h2⟩
  exact ⟨h1, Nat.le_floor h2⟩

/-! ## FRONT 1 — the classical counting bound, from the Sidon condition -/

/-- **Sidon ⇒ all differences distinct.** Stated over `ℤ` so that no `ℕ`-subtraction
truncation can hide a case. This is the difference form of the `B₂` condition, derived from
the sum form the spec fixes. -/
theorem sidon_intSub_inj {A : Set ℕ} (h : IsSidon A) {a b c d : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (heq : (a : ℤ) - (b : ℤ) = (c : ℤ) - (d : ℤ)) : a = c ∧ b = d := by
  have hsum : a + d = c + b := by omega
  rcases h a ha d hd c hc b hb hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2.symm⟩
  · exact absurd h1 hab

/-- **The counting bound, truncated form.** For a Sidon set the `k(k-1)` ordered pairs of
distinct elements of `A ∩ [1,x]` inject into the `2⌊x⌋` nonzero integers of absolute value at
most `⌊x⌋`. -/
theorem sidon_offDiag_bound {A : Set ℕ} (h : IsSidon A) (x : ℝ) :
    countUpTo A x * countUpTo A x - countUpTo A x ≤ 2 * ⌊x⌋₊ := by
  classical
  have hfin := finite_countSet A x
  have hcard : countUpTo A x = hfin.toFinset.card := by
    first
      | rw [countUpTo, Set.ncard_eq_toFinset_card _ hfin]
      | rw [countUpTo, hfin.card_toFinset]
      | simp [countUpTo, Set.ncard_eq_toFinset_card _ hfin]
      | (rw [countUpTo, Set.ncard_eq_toFinset_card']; congr 1)
      | simp [countUpTo, Set.ncard_eq_toFinset_card']
  have hT : ((Finset.Icc (-(⌊x⌋₊ : ℤ)) ((⌊x⌋₊ : ℤ))).erase 0).card = 2 * ⌊x⌋₊ := by
    rw [Finset.card_erase_of_mem (by rw [Finset.mem_Icc]; omega), Int.card_Icc]
    omega
  rw [hcard, ← Finset.offDiag_card, ← hT]
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ))
  · rintro ⟨a, b⟩ hp
    rw [Finset.mem_coe, Finset.mem_offDiag] at hp
    dsimp only at hp ⊢
    obtain ⟨ha, hb, hab⟩ := hp
    obtain ⟨-, -, ha2⟩ := hfin.mem_toFinset.mp ha
    obtain ⟨-, -, hb2⟩ := hfin.mem_toFinset.mp hb
    have haN : a ≤ ⌊x⌋₊ := Nat.le_floor ha2
    have hbN : b ≤ ⌊x⌋₊ := Nat.le_floor hb2
    rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_Icc]
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq hEq
    rw [Finset.mem_coe, Finset.mem_offDiag] at hp hq
    dsimp only at hp hq hEq
    obtain ⟨ha, hb, hab⟩ := hp
    obtain ⟨hc, hd, -⟩ := hq
    have haA := (hfin.mem_toFinset.mp ha).1
    have hbA := (hfin.mem_toFinset.mp hb).1
    have hcA := (hfin.mem_toFinset.mp hc).1
    have hdA := (hfin.mem_toFinset.mp hd).1
    obtain ⟨h1, h2⟩ := sidon_intSub_inj h haA hbA hcA hdA hab hEq
    simp only [Prod.mk.injEq]
    exact ⟨h1, h2⟩

/-- **The counting bound, subtraction-free form:** `k² ≤ k + 2⌊x⌋`. -/
theorem sidon_card_sq_le {A : Set ℕ} (h : IsSidon A) (x : ℝ) :
    countUpTo A x * countUpTo A x ≤ countUpTo A x + 2 * ⌊x⌋₊ := by
  have hb := sidon_offDiag_bound h x
  rcases Nat.eq_zero_or_pos (countUpTo A x) with h0 | hp
  · simp [h0]
  · have hsq : countUpTo A x ≤ countUpTo A x * countUpTo A x := by
      first
        | exact Nat.le_mul_of_pos_left _ hp
        | exact Nat.mul_le_mul_right _ hp
        | nlinarith
    obtain ⟨m, hm⟩ : ∃ m, countUpTo A x * countUpTo A x = m := ⟨_, rfl⟩
    rw [hm] at hb hsq ⊢
    omega

/-- **The counting bound in real form:** `|A ∩ [1,x]| ≤ √(2x) + 1` for every Sidon `A`. -/
theorem countUpTo_le_sqrt {A : Set ℕ} (h : IsSidon A) {x : ℝ} (hx : 0 ≤ x) :
    (countUpTo A x : ℝ) ≤ Real.sqrt (2 * x) + 1 := by
  have hnat := sidon_card_sq_le h x
  have hR : ((countUpTo A x : ℝ)) * (countUpTo A x : ℝ)
      ≤ (countUpTo A x : ℝ) + 2 * (⌊x⌋₊ : ℝ) := by exact_mod_cast hnat
  have hfl : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx
  have hR2 : ((countUpTo A x : ℝ)) * (countUpTo A x : ℝ)
      ≤ (countUpTo A x : ℝ) + 2 * x := by linarith
  have hsn : (0 : ℝ) ≤ Real.sqrt (2 * x) := Real.sqrt_nonneg _
  rcases le_or_gt ((countUpTo A x : ℝ)) 1 with hk1 | hk1
  · linarith
  · have hge : (0 : ℝ) ≤ (countUpTo A x : ℝ) - 1 := by linarith
    have hkey : ((countUpTo A x : ℝ) - 1) ≤ Real.sqrt (2 * x) := by
      rw [Real.le_sqrt hge (by linarith)]
      nlinarith
    linarith

/-- **The weight is `O((log x)^c)`, uniformly over all Sidon sets.** -/
theorem sidonWeight_le {A : Set ℕ} (h : IsSidon A) {c x : ℝ} (hx : 1 ≤ x) :
    sidonWeight A c x ≤ (Real.sqrt 2 + 1) * Real.log x ^ c := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hs1 : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hs0 : (0 : ℝ) < Real.sqrt x := lt_of_lt_of_le one_pos hs1
  have hnum := countUpTo_le_sqrt h (le_of_lt hx0)
  have hsq2 : Real.sqrt (2 * x) = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
  have hratio : (countUpTo A x : ℝ) / Real.sqrt x ≤ Real.sqrt 2 + 1 := by
    rw [div_le_iff₀ hs0]
    have hexp : Real.sqrt (2 * x) + 1 ≤ (Real.sqrt 2 + 1) * Real.sqrt x := by
      rw [hsq2]; nlinarith [Real.sqrt_nonneg 2]
    linarith
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hpow : (0 : ℝ) ≤ Real.log x ^ c := Real.rpow_nonneg hlog c
  exact mul_le_mul_of_nonneg_right hratio hpow

/-! ## FRONT 2 — the exponent is monotone, so a `c ≤ 1/2` witness upgrades to `c = 1/2` -/

/-- For `x ≥ e` (so `log x ≥ 1`) the weight is monotone increasing in the exponent. -/
theorem sidonWeight_mono_exponent (A : Set ℕ) {c c' x : ℝ} (hcc : c ≤ c')
    (hx : Real.exp 1 ≤ x) : sidonWeight A c x ≤ sidonWeight A c' x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hpow : Real.log x ^ c ≤ Real.log x ^ c' :=
    Real.rpow_le_rpow_of_exponent_le hlog1 hcc
  have hnn : (0 : ℝ) ≤ (countUpTo A x : ℝ) / Real.sqrt x := by positivity
  exact mul_le_mul_of_nonneg_left hpow hnn

/-- **THE UPGRADE.** An eventual positive lower bound at ANY exponent `c ≤ 1/2` is
automatically an eventual positive lower bound at exponent `1/2`. Junk-free: this is a
statement about the weight itself, not about `liminf`. -/
theorem eventually_le_half_of_eventually_le {A : Set ℕ} {c ε : ℝ} (hc : c ≤ 1 / 2)
    (h : ∀ᶠ x in (atTop : Filter ℝ), ε ≤ sidonWeight A c x) :
    ∀ᶠ x in (atTop : Filter ℝ), ε ≤ sidonWeight A (1 / 2) x := by
  filter_upwards [h, eventually_ge_atTop (Real.exp 1)] with x hx1 hx2
  exact hx1.trans (sidonWeight_mono_exponent A hc hx2)

/-! ## FRONT 3 — the liminf junk gate named in the spec header, made into a theorem -/

/-- **The junk gate, characterised.** Mathlib's `liminf` on `ℝ` is `sSup` of the set of
eventual lower bounds, and `Real.sSup` returns `0` on an unbounded set. That failure mode
happens for EXACTLY one reason: the function tends to `+∞`. -/
theorem bddAbove_liminfSet_iff (f : ℝ → ℝ) :
    BddAbove {a : ℝ | ∀ᶠ x in (atTop : Filter ℝ), a ≤ f x} ↔ ¬ Tendsto f atTop atTop := by
  constructor
  · rintro ⟨M, hM⟩ hT
    have hmem : M + 1 ∈ {a : ℝ | ∀ᶠ x in (atTop : Filter ℝ), a ≤ f x} :=
      tendsto_atTop.mp hT (M + 1)
    have := hM hmem
    linarith
  · intro hT
    rw [tendsto_atTop] at hT
    simp only [not_forall] at hT
    obtain ⟨M, hM⟩ := hT
    refine ⟨M, fun a ha => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hM (ha.mono fun x hx => le_trans (le_of_lt hlt) hx)

/-- With the junk gate discharged, an eventual lower bound really is a `liminf` lower bound. -/
theorem le_liminf_of_eventually_le_of_not_tendsto {f : ℝ → ℝ} {ε : ℝ}
    (h : ∀ᶠ x in (atTop : Filter ℝ), ε ≤ f x) (hT : ¬ Tendsto f atTop atTop) :
    ε ≤ liminf f atTop := by
  rw [Filter.liminf_eq]
  exact le_csSup ((bddAbove_liminfSet_iff f).mpr hT) h

/-! ## THE JOIN — what a `Question2`-style witness at `c ≤ 1/2` would do to `Question1` -/

/-- **CONDITIONAL.** A `Question2'`-style witness at any exponent `c ≤ 1/2`, together with the
junk gate at exponent `1/2`, REFUTES `Question1`. The hypothesis `hgate` is displayed, not
hidden: it is exactly the content of the (unproved, published) Erdős bound. -/
theorem not_question1_of_witness {A : Set ℕ} {c ε : ℝ}
    (hA : A.Infinite) (hS : IsSidon A) (hc : c ≤ 1 / 2) (hε : 0 < ε)
    (hlb : ∀ᶠ x in (atTop : Filter ℝ), ε ≤ sidonWeight A c x)
    (hgate : ¬ Tendsto (sidonWeight A (1 / 2)) atTop atTop) : ¬ Question1 := by
  intro hQ
  have h1 : liminf (sidonWeight A (1 / 2)) atTop = 0 := hQ A hA hS
  have h2 := le_liminf_of_eventually_le_of_not_tendsto
    (eventually_le_half_of_eventually_le hc hlb) hgate
  rw [h1] at h2
  linarith

/-- **CONDITIONAL.** The junk-free `Question2'` witness upgrades to the `liminf` form
`Question2`, given the gate at its own exponent. This is the missing half of the equivalence
the spec header declines to assert. -/
theorem question2_of_witness {A : Set ℕ} {c ε : ℝ}
    (hA : A.Infinite) (hS : IsSidon A) (hc : 0 < c) (hε : 0 < ε)
    (hlb : ∀ᶠ x in (atTop : Filter ℝ), ε ≤ sidonWeight A c x)
    (hgate : ¬ Tendsto (sidonWeight A c) atTop atTop) : Question2 :=
  ⟨A, hA, hS, c, hc, lt_of_lt_of_le hε (le_liminf_of_eventually_le_of_not_tendsto hlb hgate)⟩

/-! ## FRONT 1 ⊗ FRONT 3 — the gate IS dischargeable at exponent 0, unconditionally -/

theorem sidonWeight_zero_le {A : Set ℕ} (h : IsSidon A) {x : ℝ} (hx : 1 ≤ x) :
    sidonWeight A 0 x ≤ Real.sqrt 2 + 1 := by
  have hb := sidonWeight_le h (c := 0) hx
  rwa [Real.rpow_zero, mul_one] at hb

theorem not_tendsto_sidonWeight_zero {A : Set ℕ} (h : IsSidon A) :
    ¬ Tendsto (sidonWeight A 0) atTop atTop := by
  intro hT
  obtain ⟨x, hxa, hxb⟩ :=
    ((tendsto_atTop.mp hT (Real.sqrt 2 + 2)).and (eventually_ge_atTop (1 : ℝ))).exists
  have := sidonWeight_zero_le h hxb
  linarith

/-- **THE EXPONENT-0 CASE OF THE ERDŐS BOUND, PROVED.** This is the spec's sorried
`erdos_liminf_sqrt_log_le_const` with the exponent `1/2` replaced by `0` — same shape, no
`sorry`. It localises the whole difficulty of that theorem in the `(log x)^{1/2}` factor. -/
theorem liminf_sidonWeight_zero_le_const :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Set ℕ, A.Infinite → IsSidon A →
      liminf (sidonWeight A 0) atTop ≤ C := by
  refine ⟨Real.sqrt 2 + 1, by positivity, fun A _ h => ?_⟩
  rw [Filter.liminf_eq]
  apply csSup_le
  · refine ⟨0, ?_⟩
    show ∀ᶠ x in (atTop : Filter ℝ), (0 : ℝ) ≤ sidonWeight A 0 x
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x _
    simp only [sidonWeight, Real.rpow_zero, mul_one]
    positivity
  · intro b hb
    obtain ⟨x, hxa, hxb⟩ := ((hb : ∀ᶠ x in (atTop : Filter ℝ), b ≤ sidonWeight A 0 x).and
      (eventually_ge_atTop (1 : ℝ))).exists
    exact hxa.trans (sidonWeight_zero_le h hxb)

/-! ## FIDELITY — what the Mathlib `liminf` junk value does to the two NAMED TARGETS

The spec header names the trap but asserts nothing about it. The gate above turns it into
theorems. These are statements about the FORMALISATION, not about Erdős' problem. -/

/-- If the weight blows up, Mathlib's `liminf` returns `Real.sSup`'s junk value `0`. -/
theorem liminf_eq_zero_of_tendsto_atTop {f : ℝ → ℝ} (hT : Tendsto f atTop atTop) :
    liminf f atTop = 0 := by
  rw [Filter.liminf_eq]
  first
    | exact Real.sSup_of_not_bddAbove (fun hb => (bddAbove_liminfSet_iff f).mp hb hT)
    | exact Real.sSup_of_not_bddAbove _ (fun hb => (bddAbove_liminfSet_iff f).mp hb hT)
    | (apply Real.sSup_of_not_bddAbove; exact fun hb => (bddAbove_liminfSet_iff f).mp hb hT)
    | (apply Real.sSup_def ▸ rfl)

/-- **FIDELITY FINDING 1.** On any set whose weight tends to `+∞` — the case where the
mathematician's liminf is `+∞`, i.e. maximally FAR from `0` — the formalised `Question1`
clause holds anyway, for the junk reason. -/
theorem question1_clause_holds_vacuously {A : Set ℕ}
    (hT : Tendsto (sidonWeight A (1 / 2)) atTop atTop) :
    liminf (sidonWeight A (1 / 2)) atTop = 0 :=
  liminf_eq_zero_of_tendsto_atTop hT

/-- **FIDELITY FINDING 2.** The same junk makes the spec's sorried Erdős bound hold trivially,
for EVERY nonnegative constant, on exactly those sets. -/
theorem erdos_bound_vacuous_on_blowup {A : Set ℕ}
    (hT : Tendsto (sidonWeight A (1 / 2)) atTop atTop) {C : ℝ} (hC : 0 ≤ C) :
    liminf (sidonWeight A (1 / 2)) atTop ≤ C := by
  rw [liminf_eq_zero_of_tendsto_atTop hT]; exact hC

/-- **THE REDUCTION.** `Question1` is equivalent to its own restriction to the non-blowup
case: the blowup case is already true, junk-wise. Any attack on `Question1` may assume the
gate for free — and gains nothing from the blowup sets. -/
theorem question1_iff_restricted :
    Question1 ↔ ∀ A : Set ℕ, A.Infinite → IsSidon A →
      ¬ Tendsto (sidonWeight A (1 / 2)) atTop atTop →
      liminf (sidonWeight A (1 / 2)) atTop = 0 := by
  constructor
  · intro hQ A hA hS _
    exact hQ A hA hS
  · intro hQ A hA hS
    by_cases hT : Tendsto (sidonWeight A (1 / 2)) atTop atTop
    · exact liminf_eq_zero_of_tendsto_atTop hT
    · exact hQ A hA hS hT

/-- **THE ASYMMETRY, made precise.** A blowup set can never witness `Question2` (its formalised
`liminf` is `0`), yet it can satisfy every `Question2'` clause. The two readings are therefore
NOT interchangeable — exactly what the spec header declines to assert. -/
theorem not_liminf_pos_of_blowup {A : Set ℕ} {c : ℝ}
    (hT : Tendsto (sidonWeight A c) atTop atTop) :
    ¬ (0 < liminf (sidonWeight A c) atTop) := by
  rw [liminf_eq_zero_of_tendsto_atTop hT]
  exact lt_irrefl 0

end Erdos1191

#print axioms Erdos1191.sidon_intSub_inj
#print axioms Erdos1191.sidon_offDiag_bound
#print axioms Erdos1191.sidon_card_sq_le
#print axioms Erdos1191.countUpTo_le_sqrt
#print axioms Erdos1191.sidonWeight_le
#print axioms Erdos1191.sidonWeight_mono_exponent
#print axioms Erdos1191.eventually_le_half_of_eventually_le
#print axioms Erdos1191.bddAbove_liminfSet_iff
#print axioms Erdos1191.le_liminf_of_eventually_le_of_not_tendsto
#print axioms Erdos1191.not_question1_of_witness
#print axioms Erdos1191.question2_of_witness
#print axioms Erdos1191.sidonWeight_zero_le
#print axioms Erdos1191.not_tendsto_sidonWeight_zero
#print axioms Erdos1191.liminf_sidonWeight_zero_le_const
#print axioms Erdos1191.liminf_eq_zero_of_tendsto_atTop
#print axioms Erdos1191.question1_clause_holds_vacuously
#print axioms Erdos1191.erdos_bound_vacuous_on_blowup
#print axioms Erdos1191.question1_iff_restricted
#print axioms Erdos1191.not_liminf_pos_of_blowup
