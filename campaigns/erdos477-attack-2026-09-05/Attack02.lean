import Mathlib

/-!
# Erdős 477 — the mechanism abstracted, and the exact boundary of OB2

Companion to `Attack01.lean` (which is sealed independently; nothing here is needed for it).

`Attack01` closed OB1 by an accident that is worth isolating: the difference set of a
quadratic contains a nonzero SUBGROUP. This file states the mechanism for an arbitrary tile
`B`, then re-derives the quadratic theorem as its instance — which is what turns "we proved
one theorem" into "we hold a tool, and we know exactly where it stops".

**Where it stops (OB2, degree ≥ 3) — the hypothesis `hsub` is precisely what fails.**
For `f` of degree `d`, `|(f(ℤ) - f(ℤ)) ∩ [-R, R]| = O(R^{2/d})`, which is `o(R)` once
`d ≥ 3`. A nonzero subgroup `Nℤ` has counting function `2R/|N| + O(1)`, i.e. LINEAR in `R`.
So for `d ≥ 3` no nonzero `N` can satisfy `hsub`, and this tool returns nothing — not because
the bookkeeping is harder, but because the object it needs does not exist. That is a sharper
statement of the ranking's "expensive, no mechanism", and it says which mechanism must be
replaced: something that is not a difference-set pigeonhole at all.
-/

set_option autoImplicit false

namespace Erdos477Mechanism

/-- **The mechanism.** If the difference set of a tile `B` contains a nonzero subgroup `Nℤ`,
and `B` is bounded on one side, then no `A` gives every integer a UNIQUE representation
`α + β` with `α ∈ A`, `β ∈ B`.

Uniqueness forbids `N ∣ α - α'` for distinct `α, α' ∈ A`, so `A` embeds in `ℤ / N` and is
finite, hence bounded on both sides — while `A + B` must reach past any one-sided bound. -/
theorem no_tiling_of_subgroup_diff
    (B : Set ℤ) (N : ℤ) (hN : N ≠ 0)
    (hsub : ∀ t : ℤ, ∃ x ∈ B, ∃ y ∈ B, x - y = N * t)
    (hbdd : BddBelow B ∨ BddAbove B) :
    ¬ ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.2 ∈ B ∧ n = p.1 + p.2 := by
  rintro ⟨A, hA⟩
  -- (i) distinct elements of `A` are incongruent mod `N`.
  have hdiff : ∀ α ∈ A, ∀ α' ∈ A, N ∣ (α - α') → α = α' := by
    intro α hα α' hα' hdvd
    obtain ⟨t, ht⟩ := hdvd
    obtain ⟨x, hx, y, hy, hxy⟩ := hsub t
    obtain ⟨p, -, huniq⟩ := hA (α + y)
    have h1 : ((α, y) : ℤ × ℤ) = p := huniq _ ⟨hα, hy, rfl⟩
    have h2 : ((α', x) : ℤ × ℤ) = p := huniq _ ⟨hα', hx, by linarith⟩
    have h3 := congrArg Prod.fst (h1.trans h2.symm)
    simpa using h3
  -- (ii) hence `A` is finite.
  have hNabs : (0:ℤ) < |N| := abs_pos.mpr hN
  have hinj : Set.InjOn (fun x : ℤ => x % |N|) A := by
    intro x hx y hy hxy
    have hmod : Int.ModEq |N| x y := hxy
    have h1 : |N| ∣ (y - x) := Int.ModEq.dvd hmod
    have h2 : N ∣ (y - x) := (abs_dvd _ _).mp h1
    exact (hdiff y hy x hx h2).symm
  have hfin : A.Finite := by
    refine Set.Finite.of_finite_image ?_ hinj
    refine Set.Finite.subset (Set.finite_Ico (0:ℤ) |N|) ?_
    rintro z ⟨x, -, rfl⟩
    exact ⟨Int.emod_nonneg x (abs_ne_zero.mpr hN), Int.emod_lt_of_pos x hNabs⟩
  -- (iii) a bounded `A + B` cannot cover ℤ.
  rcases hbdd with hb | hb
  · obtain ⟨lB, hlB⟩ := hb
    obtain ⟨lA, hlA⟩ := hfin.bddBelow
    obtain ⟨p, ⟨hpA, hpB, hn⟩, -⟩ := hA (lA + lB - 1)
    have h1 : lA ≤ p.1 := hlA hpA
    have h2 : lB ≤ p.2 := hlB hpB
    linarith
  · obtain ⟨uB, huB⟩ := hb
    obtain ⟨uA, huA⟩ := hfin.bddAbove
    obtain ⟨p, ⟨hpA, hpB, hn⟩, -⟩ := hA (uA + uB + 1)
    have h1 : p.1 ≤ uA := huA hpA
    have h2 : p.2 ≤ uB := huB hpB
    linarith

/-! ### The quadratic case as an instance of the mechanism -/

/-- The two-parameter difference identity: `f (r+t) - f (r-t) = (4*a*r + 2*b) * t`. -/
theorem quad_diff_identity (a b c r t : ℤ) :
    (a * (t + r) ^ 2 + b * (t + r) + c) - (a * (r - t) ^ 2 + b * (r - t) + c)
      = (4 * a * r + 2 * b) * t := by
  ring

/-- The value set of a quadratic. -/
def quadSet (a b c : ℤ) : Set ℤ := {x : ℤ | ∃ k : ℤ, x = a * k ^ 2 + b * k + c}

/-- `hsub` holds for every quadratic with `a ≠ 0`: take `r = 0` (slope `2b`) when `b ≠ 0`,
otherwise `r = 1` (slope `4a`). Since `a ≠ 0`, one of the two slopes is nonzero. -/
theorem quadSet_subgroup_diff (a b c : ℤ) (ha : a ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ t : ℤ, ∃ x ∈ quadSet a b c, ∃ y ∈ quadSet a b c, x - y = N * t := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨4 * a, mul_ne_zero (by norm_num) ha, fun t => ?_⟩
    exact ⟨_, ⟨t + 1, rfl⟩, _, ⟨1 - t, rfl⟩, by ring⟩
  · refine ⟨2 * b, mul_ne_zero (by norm_num) hb, fun t => ?_⟩
    exact ⟨_, ⟨t, rfl⟩, _, ⟨-t, rfl⟩, by ring⟩

/-- `quadSet` is bounded below when `a > 0` and above when `a < 0`. -/
theorem quadSet_bdd (a b c : ℤ) (ha : a ≠ 0) :
    BddBelow (quadSet a b c) ∨ BddAbove (quadSet a b c) := by
  rcases (show a < 0 ∨ 0 < a by omega) with h | h
  · refine Or.inr ⟨c + b ^ 2, ?_⟩
    rintro _ ⟨k, rfl⟩
    nlinarith [sq_nonneg (2 * k - b), sq_nonneg b,
      mul_nonneg (by linarith : (0:ℤ) ≤ -a - 1) (sq_nonneg k)]
  · refine Or.inl ⟨c - b ^ 2, ?_⟩
    rintro _ ⟨k, rfl⟩
    nlinarith [sq_nonneg (2 * k + b), sq_nonneg b,
      mul_nonneg (by linarith : (0:ℤ) ≤ a - 1) (sq_nonneg k)]

/-- **OB1 again, this time as a one-line instance of the mechanism.** Same statement as
`Attack01.Erdos477Attack.erdos477_no_quadratic_tiling`, proved through the abstraction. -/
theorem erdos477_no_quadratic_tiling_via_mechanism (a b c : ℤ) (ha : a ≠ 0) :
    ¬ ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ,
      p.1 ∈ A ∧ (∃ k : ℤ, p.2 = a * k ^ 2 + b * k + c) ∧ n = p.1 + p.2 := by
  obtain ⟨N, hN, hsub⟩ := quadSet_subgroup_diff a b c ha
  exact no_tiling_of_subgroup_diff (quadSet a b c) N hN hsub (quadSet_bdd a b c ha)

/-- And the sealed square case, recovered through the abstraction. -/
theorem erdos477_no_square_tiling_via_mechanism :
    ¬ ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ,
      p.1 ∈ A ∧ (∃ k : ℤ, p.2 = k ^ 2) ∧ n = p.1 + p.2 := by
  have h := erdos477_no_quadratic_tiling_via_mechanism 1 0 0 one_ne_zero
  simpa using h

end Erdos477Mechanism

#print axioms Erdos477Mechanism.no_tiling_of_subgroup_diff
#print axioms Erdos477Mechanism.quad_diff_identity
#print axioms Erdos477Mechanism.quadSet_subgroup_diff
#print axioms Erdos477Mechanism.quadSet_bdd
#print axioms Erdos477Mechanism.erdos477_no_quadratic_tiling_via_mechanism
#print axioms Erdos477Mechanism.erdos477_no_square_tiling_via_mechanism
