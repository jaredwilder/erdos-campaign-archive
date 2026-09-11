import Mathlib
open Filter Finset

-- ============ NAME PROBE for Mathlib 919544d4 ============

-- offDiag cardinality
#check @Finset.offDiag_card
#check @Finset.card_le_card_of_injOn
#check @Finset.mem_offDiag
#check @Finset.card_erase_of_mem
#check @Int.card_Icc
#check @Finset.mem_Icc
#check @Finset.mem_erase

-- ncard <-> Finset
#check @Set.ncard_eq_toFinset_card'
#check @Set.Finite.mem_toFinset
#check @Set.Finite.toFinset

-- liminf
#check @Filter.liminf_eq
#check @tendsto_atTop
#check @Filter.eventually_ge_atTop
#check @le_csSup
#check @csSup_le

-- rpow
#check @Real.rpow_zero
#check @Real.rpow_nonneg
#check @Real.rpow_le_rpow_of_exponent_le

-- sqrt
#check @Real.le_sqrt
#check @Real.le_sqrt'
#check @Real.sqrt_le_sqrt
#check @Real.sq_sqrt
#check @Real.sqrt_nonneg
#check @Real.sqrt_mul
#check @Real.sqrt_pos
#check @Real.one_le_sqrt
#check @Real.lt_sqrt

-- floor / log
#check @Nat.floor_le
#check @Nat.le_floor
#check @Real.add_one_le_exp
#check @Real.le_log_iff_exp_le
#check @Real.one_le_exp_iff_le -- may not exist
#check @Real.exp_one_lt_d9
#check @Real.log_le_log
#check @Real.le_log_iff_exp_le

-- div
#check @div_le_div_of_nonneg_left
#check @div_le_iff₀
#check @mul_le_mul_of_nonneg_right

section Probe
variable (A : Set ℕ)

def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def countSet (A : Set ℕ) (x : ℝ) : Set ℕ := {n | n ∈ A ∧ 1 ≤ n ∧ (n : ℝ) ≤ x}

theorem finite_countSet (A : Set ℕ) (x : ℝ) : (countSet A x).Finite := by
  apply Set.Finite.subset (Set.finite_Icc 1 ⌊x⌋₊)
  rintro n ⟨-, h1, h2⟩
  exact ⟨h1, Nat.le_floor h2⟩

noncomputable def countUpTo (A : Set ℕ) (x : ℝ) : ℕ := (countSet A x).ncard

-- what does ncard unfold to for a Set.Finite
example (x : ℝ) : countUpTo A x = (finite_countSet A x).toFinset.card := by
  rw [countUpTo, Set.ncard_eq_toFinset_card']
  congr 1

-- probe: 1 <= log x for x >= exp 1
example (x : ℝ) (hx : Real.exp 1 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  exact hx

-- probe: mem offDiag shape
example (s : Finset ℕ) (p : ℕ × ℕ) (h : p ∈ s.offDiag) : p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≠ p.2 := by
  simpa [Finset.mem_offDiag] using h

end Probe
