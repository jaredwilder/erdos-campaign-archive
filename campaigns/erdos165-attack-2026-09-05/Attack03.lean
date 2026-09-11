/-
# Erdős #165 — ATTACK FILE 03 (2026-09-05) · the elementary half of Shearer's estimate

Scratch/dev file for the `hest` hypothesis of `Attack02.shearer_upper_of_bound_and_estimate`.
Definitions and the `lt_shearerF` sandwich are copied from Attack02 (sealed).

⛔ SUPERSEDED — kept only as the development record. This file SEALED on its first kernel pass
(exit 0, 3 clean declarations, 0 sorryAx), which discharged `hest`; its three theorems
(`eventually_log_ge`, `scale_ge_self`, `shearer_estimate`) were then merged verbatim into §7 of
`Attack02.lean` and are verified THERE. `Attack02.log` is the receipt of record and covers them.
Do not cite this file's compile separately; re-verify via Attack02.
-/

import Mathlib
open Filter Topology

namespace Erdos165

noncomputable def scale (k : ℕ) : ℝ := (k : ℝ) ^ 2 / Real.log k

noncomputable def shearerF (x : ℝ) : ℝ := (x * Real.log x - x + 1) / (x - 1) ^ 2

/-- ⟪A02⟫ -/
theorem log_nat_pos {k : ℕ} (hk : 2 ≤ k) : 0 < Real.log k := by
  have hk1 : (1 : ℕ) < k := hk
  exact Real.log_pos (by exact_mod_cast hk1)

/-- ⟪A02⟫ -/
theorem sq_nat_pos {k : ℕ} (hk : 2 ≤ k) : (0 : ℝ) < (k : ℝ) ^ 2 := by
  have hk0 : (0 : ℕ) < k := by omega
  have hk0' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  exact pow_pos hk0' 2

/-- ⟪A02⟫ -/
theorem scale_pos {k : ℕ} (hk : 2 ≤ k) : 0 < scale k :=
  div_pos (sq_nat_pos hk) (log_nat_pos hk)

/-- ⟪A02⟫ -/
theorem scale_mul_log {k : ℕ} (hk : 2 ≤ k) : scale k * Real.log k = (k : ℝ) ^ 2 := by
  have hL : Real.log k ≠ 0 := ne_of_gt (log_nat_pos hk)
  rw [scale]
  field_simp

/-- ⟪A02⟫ The lower half of the Shearer sandwich. -/
theorem lt_shearerF {x : ℝ} (hx1 : 1 < x) : (Real.log x - 1) / (x - 1) < shearerF x := by
  have hd : (0 : ℝ) < x - 1 := by linarith
  have hsq : (0 : ℝ) < (x - 1) ^ 2 := by positivity
  have hpos : 0 < Real.log x := Real.log_pos hx1
  rw [shearerF, lt_div_iff₀ hsq]
  have heq : (Real.log x - 1) / (x - 1) * (x - 1) ^ 2 = (Real.log x - 1) * (x - 1) := by
    field_simp
  rw [heq]
  nlinarith [mul_pos hd hpos]

/-! ## NEW in Attack03. -/

/-- **NEW.** `log k → ∞`, in the only form needed: for any bound `B`, eventually `log k ≥ B`.
Proved from monotonicity of `log` at `exp B`, so no limit-composition API is used. -/
theorem eventually_log_ge (B : ℝ) : ∀ᶠ k : ℕ in atTop, B ≤ Real.log k := by
  filter_upwards [eventually_ge_atTop (⌈Real.exp B⌉₊ + 1)] with k hk
  have h1 : ((⌈Real.exp B⌉₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have h2 : Real.exp B ≤ ((⌈Real.exp B⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h3 : Real.exp B < (k : ℝ) := by linarith
  have h4 := Real.log_lt_log (Real.exp_pos B) h3
  rw [Real.log_exp] at h4
  exact h4.le

/-- **NEW.** `k²/log k ≥ k`, because `log k ≤ k − 1`. This is what makes `scale` tend to
infinity, and it is all the divergence the estimate needs. -/
theorem scale_ge_self {k : ℕ} (hk : 2 ≤ k) : (k : ℝ) ≤ scale k := by
  have hL : 0 < Real.log k := log_nat_pos hk
  have hk0' : (0 : ℕ) < k := by omega
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0'
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : (k : ℝ) ≠ 1 := by linarith
  have hlt : Real.log k < (k : ℝ) - 1 := Real.log_lt_sub_one_of_pos hk0 hk1
  rw [scale, le_div_iff₀ hL]
  nlinarith [mul_lt_mul_of_pos_left hlt hk0, hk0]

/-- **NEW — THE ELEMENTARY HALF OF SHEARER'S ESTIMATE.**
For every `ε > 0`, eventually there is an integer `n` with `k ≤ n·f(k−1)` and
`n ≤ (1+ε)·k²/log k`. Mentions no graph and no Ramsey number: it is a statement about
`shearerF` and `log` alone. Together with Shearer's finite independence inequality
(`Attack02.ShearerBound`) this gives `R(3,k) ≤ (1+o(1))k²/log k`.

The witness is `n = ⌈k/f(k−1)⌉`. The two facts driving it are the Attack02 sandwich
`f(x) > (log x − 1)/(x−1)` and `log(k−1) ≥ log k − log 2`. -/
theorem shearer_estimate (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∃ n : ℕ,
      (k : ℝ) ≤ (n : ℝ) * shearerF ((k : ℝ) - 1) ∧ (n : ℝ) ≤ (1 + ε) * scale k := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hεhalf : (0 : ℝ) ≤ ε / 2 := by linarith
  have hmul : (ε / 2) * ((1 + ε / 2) * (Real.log 2 + 1) * (2 / ε))
      = (1 + ε / 2) * (Real.log 2 + 1) := by
    first
      | (field_simp; ring)
      | field_simp
  filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop (⌈2 / ε⌉₊ + 1),
      eventually_log_ge ((1 + ε / 2) * (Real.log 2 + 1) * (2 / ε)),
      eventually_log_ge (Real.log 2 + 2)] with k hk3 hkN hLa hLb
  have hk2 : 2 ≤ k := by omega
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hL : 0 < Real.log k := log_nat_pos hk2
  have hS : 0 < scale k := scale_pos hk2
  have hSk : (k : ℝ) ≤ scale k := scale_ge_self hk2
  have hx1 : (1 : ℝ) < (k : ℝ) - 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `log (k−1) ≥ log k − log 2`, via `(k)/2 < k − 1` for `k ≥ 3`.
  have hlogx : Real.log k - Real.log 2 ≤ Real.log ((k : ℝ) - 1) := by
    have hhalf : (k : ℝ) / 2 < (k : ℝ) - 1 := by linarith
    have hpos : (0 : ℝ) < (k : ℝ) / 2 := by linarith
    have h := Real.log_lt_log hpos hhalf
    rw [Real.log_div (ne_of_gt hk0) (by norm_num)] at h
    linarith
  -- the Attack02 sandwich, cleared of its denominator
  have hk2pos : (0 : ℝ) < (k : ℝ) - 1 - 1 := by linarith
  have hfm : Real.log ((k : ℝ) - 1) - 1 < shearerF ((k : ℝ) - 1) * ((k : ℝ) - 1 - 1) :=
    (div_lt_iff₀ hk2pos).mp (lt_shearerF hx1)
  have hA : (0 : ℝ) < Real.log k - Real.log 2 - 1 := by linarith
  have hF : 0 < shearerF ((k : ℝ) - 1) := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (neg_nonneg.mpr hcon) hk2pos.le]
  have hkA : Real.log k - Real.log 2 - 1 ≤ (k : ℝ) * shearerF ((k : ℝ) - 1) := by
    nlinarith [hF, hfm, hlogx]
  -- `log k ≤ (1 + ε/2)·(log k − log 2 − 1)`, from `log k` being large
  have h1 : (ε / 2) * ((1 + ε / 2) * (Real.log 2 + 1) * (2 / ε)) ≤ (ε / 2) * Real.log k :=
    mul_le_mul_of_nonneg_left hLa hεhalf
  rw [hmul] at h1
  have key : Real.log k ≤ (1 + ε / 2) * (Real.log k - Real.log 2 - 1) := by nlinarith [h1]
  have hSL : Real.log k * scale k = (k : ℝ) ^ 2 := by
    rw [mul_comm]
    exact scale_mul_log hk2
  -- (a) `k / f(k−1) ≤ (1 + ε/2)·scale k`
  have hstepA : (k : ℝ) / shearerF ((k : ℝ) - 1) ≤ (1 + ε / 2) * scale k := by
    rw [div_le_iff₀ hF]
    have e1 : (Real.log k - Real.log 2 - 1) * scale k
        ≤ ((k : ℝ) * shearerF ((k : ℝ) - 1)) * scale k :=
      mul_le_mul_of_nonneg_right hkA hS.le
    have e1' : (1 + ε / 2) * ((Real.log k - Real.log 2 - 1) * scale k)
        ≤ (1 + ε / 2) * (((k : ℝ) * shearerF ((k : ℝ) - 1)) * scale k) :=
      mul_le_mul_of_nonneg_left e1 (by linarith)
    have e2 : Real.log k * scale k
        ≤ ((1 + ε / 2) * (Real.log k - Real.log 2 - 1)) * scale k :=
      mul_le_mul_of_nonneg_right key hS.le
    have e3 : (k : ℝ) ^ 2
        ≤ (1 + ε / 2) * ((k : ℝ) * shearerF ((k : ℝ) - 1) * scale k) := by
      nlinarith [e1', e2, hSL]
    nlinarith [e3, hk0, mul_pos hk0 hk0]
  -- (b) `1 ≤ (ε/2)·scale k`
  have hstepB : (1 : ℝ) ≤ (ε / 2) * scale k := by
    have hc1 : (2 / ε) ≤ ((⌈2 / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hc2 : ((⌈2 / ε⌉₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hkN
    have hc3 : (2 / ε) ≤ scale k := by linarith
    have hc4 : (ε / 2) * (2 / ε) ≤ (ε / 2) * scale k := mul_le_mul_of_nonneg_left hc3 hεhalf
    have hc5 : (ε / 2) * (2 / ε) = 1 := by
      first
        | (field_simp; ring)
        | field_simp
    linarith
  -- the witness
  refine ⟨⌈(k : ℝ) / shearerF ((k : ℝ) - 1)⌉₊, ?_, ?_⟩
  · have hle : (k : ℝ) / shearerF ((k : ℝ) - 1)
        ≤ ((⌈(k : ℝ) / shearerF ((k : ℝ) - 1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    exact (div_le_iff₀ hF).mp hle
  · have hnn : (0 : ℝ) ≤ (k : ℝ) / shearerF ((k : ℝ) - 1) := le_of_lt (div_pos hk0 hF)
    have hceil : ((⌈(k : ℝ) / shearerF ((k : ℝ) - 1)⌉₊ : ℕ) : ℝ)
        < (k : ℝ) / shearerF ((k : ℝ) - 1) + 1 := Nat.ceil_lt_add_one hnn
    linarith

end Erdos165

#print axioms Erdos165.eventually_log_ge
#print axioms Erdos165.scale_ge_self
#print axioms Erdos165.shearer_estimate
