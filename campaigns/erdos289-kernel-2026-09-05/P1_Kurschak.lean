import Mathlib

/-!
# Erdős 289 campaign — lemma **P1**, kernel formalization (2026-09-05)

Campaign of record: `erdos289-campaign-001`, route **R008**, lemma **P1**, registry seq 48,
recorded status `PROVED` with the explicit annotation **"NOT kernel-checked."**
This file closes exactly that gap.

## The campaign's P1, verbatim (routes/registry.jsonl, seq 48)

> "p-adic numerator obstruction, every prime: if S is a finite set of integers >= 2 with
> sum_{n in S} 1/n in Z, then for every prime p, with A_p = {n/p : n in S, p | n},
> v_p(sum_{m in A_p} 1/m) >= 1. Elementary (only multiples of p carry negative v_p;
> factor 1/p; induct through A_p). p = 2 instance is Kurschak 1918 = the campaign's
> R002/R003/R004 L1."

## What is proved here (a ladder, strongest first)

* `P1_pIntegral_num` — **strongest**. Hypothesis weakened from "the sum is an integer" to
  "the sum is `p`-integral" (`PInt`, below). Conclusion in numerator form: `(p:ℤ) ∣ T.num`.
* `P1_num` — the campaign's integer hypothesis, numerator conclusion. `2 ≤ n` NOT needed.
* `P1` — the campaign's literal form: `1 ≤ padicValRat p T`, with `2 ≤ n` and `A_p ≠ ∅`.
* `P1_kurschak_two` — the `p = 2` instance (Kürschák 1918), by specialisation.

## Method

`p`-integrality is carried as an EXISTENTIAL (`PInt`): a rational is `p`-integral iff it can be
written `a / b` with `p ∤ b`. Closure under `+` is then one `div_add_div` plus
`Nat.Prime.dvd_mul`, and the descent is one cross-multiplication plus Euclid in `ℕ`.
No `Rat.den` arithmetic is needed anywhere.

The mathematics, in one line: `∑_{n ∈ S} 1/n = X + T/p` where `X` collects the `n` prime to `p`
(so `X` is `p`-integral) and `T = ∑_{m ∈ A_p} 1/m`. If the total is `p`-integral then so is
`T/p`, i.e. `v_p(T) ≥ 1`.

See §DELTA at the foot of the file for the statement-fidelity record.
-/

open Finset

namespace Erdos289

/-- `PInt p q`: the rational `q` admits a representation `a / b` with `p ∤ b` — i.e. `q` is
`p`-integral.  Carried existentially so that no `Rat.den` API is needed. -/
def PInt (p : ℕ) (q : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, b ≠ 0 ∧ ¬ (p ∣ b) ∧ q = (a : ℚ) / (b : ℚ)

theorem PInt.zero {p : ℕ} (hp : p.Prime) : PInt p 0 :=
  ⟨0, 1, one_ne_zero, fun h => hp.ne_one (Nat.dvd_one.mp h), by norm_num⟩

theorem PInt.intCast {p : ℕ} (hp : p.Prime) (z : ℤ) : PInt p (z : ℚ) :=
  ⟨z, 1, one_ne_zero, fun h => hp.ne_one (Nat.dvd_one.mp h), by norm_num⟩

theorem PInt.inv_natCast {p n : ℕ} (h : ¬ (p ∣ n)) : PInt p ((n : ℚ))⁻¹ := by
  refine ⟨1, n, ?_, h, ?_⟩
  · rintro rfl
    exact h (dvd_zero p)
  · norm_num

theorem PInt.neg {p : ℕ} {q : ℚ} (hq : PInt p q) : PInt p (-q) := by
  obtain ⟨a, b, hb0, hb, rfl⟩ := hq
  exact ⟨-a, b, hb0, hb, by push_cast; ring⟩

theorem PInt.add {p : ℕ} (hp : p.Prime) {q r : ℚ} (hq : PInt p q) (hr : PInt p r) :
    PInt p (q + r) := by
  obtain ⟨a, b, hb0, hb, rfl⟩ := hq
  obtain ⟨c, d, hd0, hd, rfl⟩ := hr
  have hbQ : ((b : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hb0
  have hdQ : ((d : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  refine ⟨a * (d : ℤ) + (b : ℤ) * c, b * d, Nat.mul_ne_zero hb0 hd0, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact hb h1
    · exact hd h1
  · rw [div_add_div _ _ hbQ hdQ]
    push_cast
    ring

theorem PInt.sum {p : ℕ} (hp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, PInt p (f i)) : PInt p (∑ i ∈ s, f i) :=
  Finset.sum_induction f (PInt p) (fun _ _ ha hb => PInt.add hp ha hb) (PInt.zero hp) h

/-- A reciprocal sum over integers prime to `p` is `p`-integral. -/
theorem PInt.sum_inv {p : ℕ} (hp : p.Prime) (G : Finset ℕ) (hG : ∀ n ∈ G, ¬ p ∣ n) :
    PInt p (∑ n ∈ G, ((n : ℚ))⁻¹) :=
  PInt.sum hp G _ (fun n hn => PInt.inv_natCast (hG n hn))

/-- The cofactor set `A_p = { n / p : n ∈ S, p ∣ n }` of the campaign statement. -/
def cofactors (p : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (S.filter (fun n => p ∣ n)).image (fun n => n / p)

/-- Factoring out `1/p`: `∑_{m ∈ A_p} 1/m = p · ∑_{n ∈ S, p ∣ n} 1/n`. -/
theorem sum_cofactors (p : ℕ) (hp : p.Prime) (S : Finset ℕ) :
    ∑ m ∈ cofactors p S, ((m : ℚ))⁻¹
      = (p : ℚ) * ∑ n ∈ S.filter (fun n => p ∣ n), ((n : ℚ))⁻¹ := by
  have hpQ : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hinj : Set.InjOn (fun n => n / p) (↑(S.filter (fun n => p ∣ n)) : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : p ∣ x := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    have hy' : p ∣ y := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    have hxy' : x / p = y / p := hxy
    calc x = x / p * p := (Nat.div_mul_cancel hx').symm
      _ = y / p * p := by rw [hxy']
      _ = y := Nat.div_mul_cancel hy'
  unfold cofactors
  rw [Finset.sum_image hinj, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hpn : p ∣ n := (Finset.mem_filter.mp hn).2
  rw [Nat.cast_div hpn hpQ, inv_div, div_eq_mul_inv]

/-- Descent step: if `T = p · Y` with `Y` `p`-integral, then `p` divides the numerator of `T`. -/
theorem num_dvd_of_eq_mul {p : ℕ} (hp : p.Prime) {T Y : ℚ} (hY : PInt p Y)
    (hT : T = (p : ℚ) * Y) : (p : ℤ) ∣ T.num := by
  obtain ⟨a, b, hb0, hb, rfl⟩ := hY
  have hbQ : ((b : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hb0
  have hTdQ : ((T.den : ℚ)) ≠ 0 := by
    have h : T.den ≠ 0 := Rat.den_ne_zero T
    exact_mod_cast h
  have hTb : T * (b : ℚ) = (p : ℚ) * (a : ℚ) := by
    rw [hT]
    field_simp
  have hnum : (T.num : ℚ) = T * (T.den : ℚ) := by
    have h0 := Rat.num_div_den T
    rw [div_eq_iff hTdQ] at h0
    exact h0
  have key : (T.num : ℚ) * (b : ℚ) = ((p : ℚ) * (a : ℚ)) * (T.den : ℚ) := by
    rw [hnum, mul_right_comm, hTb]
  have key' : T.num * (b : ℤ) = ((p : ℤ) * a) * (T.den : ℤ) := by exact_mod_cast key
  have keyN : T.num.natAbs * b = p * a.natAbs * T.den := by
    have h6 := congrArg Int.natAbs key'
    simpa [Int.natAbs_mul] using h6
  have hpdvd : p ∣ T.num.natAbs * b := ⟨a.natAbs * T.den, by rw [keyN]; ring⟩
  have hfin : p ∣ T.num.natAbs := ((Nat.Prime.dvd_mul hp).mp hpdvd).resolve_right hb
  exact Int.natAbs_dvd_natAbs.mp (by simpa using hfin)

/-- **P1, strongest form.**  If `∑_{n ∈ S} 1/n` is `p`-integral then `p` divides the numerator
of `∑_{m ∈ A_p} 1/m`, where `A_p = { n/p : n ∈ S, p ∣ n }`.  No hypothesis on the elements of
`S`, and none on `A_p` being nonempty. -/
theorem P1_pIntegral_num {p : ℕ} (hp : p.Prime) (S : Finset ℕ)
    (hint : PInt p (∑ n ∈ S, ((n : ℚ))⁻¹)) :
    (p : ℤ) ∣ (∑ m ∈ cofactors p S, ((m : ℚ))⁻¹).num := by
  have hFint : PInt p (∑ n ∈ S.filter (fun n => p ∣ n), ((n : ℚ))⁻¹) := by
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not S (fun n => p ∣ n) (fun n => ((n : ℚ))⁻¹)
    have hGint : PInt p (∑ n ∈ S.filter (fun n => ¬ p ∣ n), ((n : ℚ))⁻¹) :=
      PInt.sum_inv hp _ (fun n hn => (Finset.mem_filter.mp hn).2)
    have heq : (∑ n ∈ S.filter (fun n => p ∣ n), ((n : ℚ))⁻¹)
        = (∑ n ∈ S, ((n : ℚ))⁻¹) + -(∑ n ∈ S.filter (fun n => ¬ p ∣ n), ((n : ℚ))⁻¹) := by
      rw [← hsplit]
      ring
    rw [heq]
    exact PInt.add hp hint (PInt.neg hGint)
  exact num_dvd_of_eq_mul hp hFint (sum_cofactors p hp S)

/-- **P1, campaign hypothesis, numerator form.**  If `∑_{n ∈ S} 1/n` is the integer `N`, then
`p` divides the numerator of `∑_{m ∈ A_p} 1/m`.  (The campaign's `2 ≤ n` is not needed, and
`A_p` may be empty.) -/
theorem P1_num {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (N : ℤ)
    (hsum : ∑ n ∈ S, ((n : ℚ))⁻¹ = (N : ℚ)) :
    (p : ℤ) ∣ (∑ m ∈ cofactors p S, ((m : ℚ))⁻¹).num := by
  refine P1_pIntegral_num hp S ?_
  rw [hsum]
  exact PInt.intCast hp N

/-- Numerator divisibility upgrades to the valuation statement `v_p ≥ 1`. -/
theorem one_le_padicValRat_of_num_dvd {p : ℕ} (hp : p.Prime) {q : ℚ} (hq : q ≠ 0)
    (h : (p : ℤ) ∣ q.num) : 1 ≤ padicValRat p q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnum0 : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hnumAbs : p ∣ q.num.natAbs := by
    have h' := Int.natAbs_dvd_natAbs.mpr h
    simpa using h'
  have hden : ¬ (p ∣ q.den) := by
    intro hd
    have hg : Nat.gcd q.num.natAbs q.den = 1 := q.reduced
    have hdg := Nat.dvd_gcd hnumAbs hd
    rw [hg] at hdg
    exact hp.ne_one (Nat.dvd_one.mp hdg)
  have h1 : 1 ≤ padicValNat p q.num.natAbs :=
    one_le_padicValNat_of_dvd (Int.natAbs_pos.mpr hnum0).ne' hnumAbs
  have h2 : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd hden
  unfold padicValRat padicValInt
  rw [h2]
  omega

/-- **P1, campaign-literal form.**  `S` a finite set of integers `≥ 2` whose reciprocal sum is an
integer, `p` prime, `A_p = { n/p : n ∈ S, p ∣ n }` nonempty.  Then
`v_p(∑_{m ∈ A_p} 1/m) ≥ 1`. -/
theorem P1 {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (hS : ∀ n ∈ S, 2 ≤ n) (N : ℤ)
    (hsum : ∑ n ∈ S, ((n : ℚ))⁻¹ = (N : ℚ)) (hne : (cofactors p S).Nonempty) :
    1 ≤ padicValRat p (∑ m ∈ cofactors p S, ((m : ℚ))⁻¹) := by
  have hpos : 0 < ∑ m ∈ cofactors p S, ((m : ℚ))⁻¹ := by
    refine Finset.sum_pos ?_ hne
    intro m hm
    have hm1 : 0 < m := by
      unfold cofactors at hm
      obtain ⟨n, hn, hnm⟩ := Finset.mem_image.mp hm
      have hnm' : n / p = m := hnm
      have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
      have hpn : p ∣ n := (Finset.mem_filter.mp hn).2
      have hn2 : 2 ≤ n := hS n hnS
      have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
      rw [← hnm']
      exact Nat.div_pos hpn' hp.pos
    have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm1
    exact inv_pos.mpr hmQ
  exact one_le_padicValRat_of_num_dvd hp (ne_of_gt hpos) (P1_num hp S N hsum)

/-- **Kürschák 1918**, the `p = 2` instance of P1 — the ancestor of the campaign's
R002/R003/R004 lemma L1, obtained here by specialisation, not by a separate argument. -/
theorem P1_kurschak_two (S : Finset ℕ) (hS : ∀ n ∈ S, 2 ≤ n) (N : ℤ)
    (hsum : ∑ n ∈ S, ((n : ℚ))⁻¹ = (N : ℚ)) (hne : (cofactors 2 S).Nonempty) :
    1 ≤ padicValRat 2 (∑ m ∈ cofactors 2 S, ((m : ℚ))⁻¹) :=
  P1 Nat.prime_two S hS N hsum hne

/-! ### Non-vacuity witness

A formalization whose hypotheses are unsatisfiable is vacuously true and worthless.  `S = {2,3,6}`
inhabits every hypothesis of `P1` at once: `1/2 + 1/3 + 1/6 = 1` exactly, every element is `≥ 2`,
and `A_p ≠ ∅` for `p ∈ {2,3}`.  (`A_2 = {1,3}`, sum `4/3`, numerator `4`;
`A_3 = {1,2}`, sum `3/2`, numerator `3`.)  Both instances are discharged below. -/

theorem witness_sum : ∑ n ∈ ({2, 3, 6} : Finset ℕ), ((n : ℚ))⁻¹ = ((1 : ℤ) : ℚ) := by
  norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]

theorem witness_ge_two : ∀ n ∈ ({2, 3, 6} : Finset ℕ), 2 ≤ n := by decide

theorem witness_P1_three :
    1 ≤ padicValRat 3 (∑ m ∈ cofactors 3 ({2, 3, 6} : Finset ℕ), ((m : ℚ))⁻¹) :=
  P1 (by norm_num) _ witness_ge_two 1 witness_sum ⟨1, by decide⟩

theorem witness_P1_kurschak_two :
    1 ≤ padicValRat 2 (∑ m ∈ cofactors 2 ({2, 3, 6} : Finset ℕ), ((m : ℚ))⁻¹) :=
  P1_kurschak_two _ witness_ge_two 1 witness_sum ⟨1, by decide⟩

end Erdos289

/-! §DELTA — statement fidelity against the campaign prose, recorded rather than absorbed.

  (a) `A_p = ∅`.  The campaign asserts `v_p ≥ 1` unconditionally.  Mathlib sets
      `padicValRat p 0 = 0`, so the literal inequality is FALSE when `A_p = ∅` (then `T = 0`).
      `P1` therefore carries `(cofactors p S).Nonempty` — which is exactly the case split the
      campaign's own operational restatement uses ("either A is empty or p divides the numerator",
      `kernel/search-2026-09-02/SEARCH-REPORT-2026-09-02.md` §2).  `P1_num` avoids the issue
      entirely: `p ∣ 0`, so the numerator form needs no nonemptiness hypothesis.
  (b) `2 ≤ n` for `n ∈ S`.  Assumed by the campaign; needed here ONLY to force `T > 0` in the
      `padicValRat` form.  `P1_num` and `P1_pIntegral_num` do not assume it.
  (c) `∑ 1/n ∈ ℤ`.  Weakened to `p`-integrality of the sum in `P1_pIntegral_num`.
  (d) The search report's side condition `p² > B` is NOT needed and is not assumed: it belongs to
      the *element ban* C1 built on top of P1, not to P1 itself.  The proof here never uses
      `v_p(n) = 1` for `n ∈ S`.

  Net: (a) is a repair of a false edge case; (b), (c), (d) are strengthenings.  Nothing in the
  campaign's P1 is weakened.
-/

#print axioms Erdos289.PInt.add
#print axioms Erdos289.PInt.sum
#print axioms Erdos289.PInt.sum_inv
#print axioms Erdos289.sum_cofactors
#print axioms Erdos289.num_dvd_of_eq_mul
#print axioms Erdos289.P1_pIntegral_num
#print axioms Erdos289.P1_num
#print axioms Erdos289.one_le_padicValRat_of_num_dvd
#print axioms Erdos289.P1
#print axioms Erdos289.P1_kurschak_two
#print axioms Erdos289.witness_sum
#print axioms Erdos289.witness_P1_three
#print axioms Erdos289.witness_P1_kurschak_two
