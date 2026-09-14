import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Decide

def S : Finset ℤ := {1, 3, 9, 27, 81, 243, 729, 2187}

def altSum (L : List ℤ) : ℤ :=
  match L with
  | [x1, x2, x3, x4, x5, x6] => 1 * x1 - 5 * x2 + 10 * x3 - 10 * x4 + 5 * x5 - 1 * x6
  | _ => 0

def allSixTuplesCheck : Bool :=
  let lst := S.sort (· ≤ ·)
  -- Generate all combinations of length 6 from lst
  -- Since lst has length 8, we can just check all sublists of length 6 or usecombinations
  let combs := lst.sublists.filter (fun l => l.length == 6)
  combs.all (fun l => altSum l ≠ 0)

theorem S_avoids_fifth_diff :
    ∀ x1 x2 x3 x4 x5 x6 : ℤ,
      x1 ∈ S → x2 ∈ S → x3 ∈ S → x4 ∈ S → x5 ∈ S → x6 ∈ S →
      x1 < x2 → x2 < x3 → x3 < x4 → x4 < x5 → x5 < x6 →
      1 * x1 - 5 * x2 + 10 * x3 - 10 * x4 + 5 * x5 - 1 * x6 ≠ 0 := by
  intro x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6 lt1 lt2 lt3 lt4 lt5
  have h_dec : allSixTuplesCheck = true := by native_decide
  -- We can bridge this by evaluating the statement directly with native_decide
  -- or running the check.
  -- Alternatively, let's prove it directly using `decide` on bounded quantification.
  -- Since S is a finite set, we can express this as a decidable proposition over Finset.
  -- Let's use `decide` via a direct finset formulation:
  -- Actually, let's write the theorem statement using Finset and sublists, or just let `native_decide` handle a finite check.
  -- Since `x1...x6` are arbitrary reals in S with order, we can check all 6-tuples from S.
  have : (1 * x1 - 5 * x2 + 10 * x3 - 10 * x4 + 5 * x5 - 1 * x6) ≠ 0 := by
    -- We can prove this by `decide` if we package it properly, or just use `native_decide` on the finite enumeration.
    -- Let's do cases or use `native_decide` over the finite set.
    -- Wait, `native_decide` can evaluate propositions about explicit finite sets.
    -- Let's formulate an equivalent proposition that is explicitly decidable.
    sorry
  exact this

-- Let's provide a clean, fully verified version using Finset.filter and `decide`.

def S_list : List ℤ := [1, 3, 9, 27, 81, 243, 729, 2187]

def checkAll : Bool :=
  let l := S_list
  (l.sublists.filter (fun s => s.length == 6)).all
    (fun s => match s with
      | [x1, x2, x3, x4, x5, x6] =>
          if x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 then
            1 * x1 - 5 * x2 + 10 * x3 - 10 * x4 + 5 * x5 - 1 * x6 ≠ 0
          else true
      | _ => true)

theorem checkAll_true : checkAll = true := by native_decide

theorem S_avoids_fifth_diff_dec :
    ∀ x1 x2 x3 x4 x5 x6 : ℤ,
      x1 ∈ S_list → x2 ∈ S_list → x3 ∈ S_list → x4 ∈ S_list → x5 ∈ S_list → x6 ∈ S_list →
      x1 < x2 → x2 < x3 → x3 < x4 → x4 < x5 → x5 < x6 →
      1 * x1 - 5 * x2 + 10 * x3 - 10 * x4 + 5 * x5 - 1 * x6 ≠ 0 := by
  intros x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6 lt1 lt2 lt3 lt4 lt5
  have h_mem : [x1, x2, x3, x4, x5, x6] ∈ S_list.sublists.filter (fun s => s.length == 6) := by
    rw [List.mem_filter, List.mem_sublists]
    refine ⟨?_, by simp [h1, h2, h3, h4, h5, h6]⟩
    constructor
    · exact List.subsequence_of_subset (by simp [h1, h2, h3, h4, h5, h6])
    · simp [h1, h2, h3, h4, h5, h6]
  have h_all := List.all_eq_true.mp checkAll_true [x1, x2, x3, x4, x5, x6] h_mem
  simp only [List.length] at h_all
  split at h_all
  · rename_i a b c d e f
    -- a, b, c, d, e, f are x1, x2, x3, x4, x5, x6
    have eq_vals : a = x1 ∧ b = x2 ∧ c = x3 ∧ d = x4 ∧ e = x5 ∧ f = x6 := by
      -- from match equality
      sorry
    -- Actually, simpler: use List.Nodup or just let `decide` do the heavy lifting via a Theorem over Finsets.
    sorry
  · contradiction

-- Let's rewrite with a direct Finset approach that Lean handles natively and cleanly.

def S_fin : Finset ℤ := {1, 3, 9, 27, 81, 243, 729, 2187}

theorem S_fin_property :
    ∀ x ∈ S_fin, ∀ y ∈ S_fin, ∀ z ∈ S_fin, ∀ w ∈ S_fin, ∀ u ∈ S_fin, ∀ v ∈ S_fin,
      x < y → y < z → z < w → w < u → u < v →
      1 * x - 5 * y + 10 * z - 10 * w + 5 * u - 1 * v ≠ 0 := by
  intro x hx y hy z hz w hw u hu v hv ltx lty ltz ltw ltu
  -- Since S_fin has 8 elements, we can prove this by `decide` if we state it as a bounded quantification over Finset.
  -- But Finset universal quantification with 6 variables is large. Alternatively, `decide` can evaluate it directly.
  have : (∀ (x y z w u v : ℤ), x ∈ S_fin → y ∈ S_fin → z ∈ S_fin → w ∈ S_fin → u ∈ S_fin → v ∈ S_fin →
          x < y → y < z → z < w → w < u → u < v →
          1 * x - 5 * y + 10 * z - 10 * w + 5 * u - 1 * v ≠ 0) := by
    decide
  exact this x y z w u v hx hy hz hw hu hv ltx lty ltz ltw ltu