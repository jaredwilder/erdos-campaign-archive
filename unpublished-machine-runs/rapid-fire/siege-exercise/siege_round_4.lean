import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Decide

def S_fin : Finset ℤ := {1, 3, 9, 27, 81, 243, 729, 2187}

theorem S_avoids_fifth_diff :
    ∀ x1 x2 x3 x4 x5 x6 : ℤ,
      x1 ∈ S_fin → x2 ∈ S_fin → x3 ∈ S_fin → x4 ∈ S_fin → x5 ∈ S_fin → x6 ∈ S_fin →
      x1 < x2 → x2 < x3 → x3 < x4 → x4 < x5 → x5 < x6 →
      1 * x1 - 5 * x2 + 10 * x3 - 10 * x4 + 5 * x5 - 1 * x6 ≠ 0 := by
  have h : ∀ (x1 x2 x3 x4 x5 x6 : ℤ),
      x1 ∈ S_fin → x2 ∈ S_fin → x3 ∈ S_fin → x4 ∈ S_fin → x5 ∈ S_fin → x6 ∈ S_fin →
      x1 < x2 → x2 < x3 → x3 < x4 → x4 < x5 → x5 < x6 →
      1 * x1 - 5 * x2 + 10 * x3 - 10 * x4 + 5 * x5 - 1 * x6 ≠ 0 := by
    decide
  exact fun x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6 lt1 lt2 lt3 lt4 lt5 =>
    h x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6 lt1 lt2 lt3 lt4 lt5