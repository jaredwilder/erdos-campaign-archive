import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Decide

def S : List ℤ := [1, 3, 9, 27, 81, 243, 729, 2187]

def altSum6 (x1 x2 x3 x4 x5 x6 : ℤ) : ℤ :=
  1 * x1 - 5 * x2 + 10 * x3 - 10 * x4 + 5 * x5 - 1 * x6

def allCheck : Bool :=
  (S.sublists.filter (fun l => l.length == 6)).all (fun l =>
    match l with
    | [x1, x2, x3, x4, x5, x6] =>
      if x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 then
        altSum6 x1 x2 x3 x4 x5 x6 ≠ 0
      else
        true
    | _ => true)

theorem allCheck_true : allCheck = true := by
  native_decide

theorem S_avoids_fifth_diff (x1 x2 x3 x4 x5 x6 : ℤ)
    (h1 : x1 ∈ S) (h2 : x2 ∈ S) (h3 : x3 ∈ S)
    (h4 : x4 ∈ S) (h5 : x5 ∈ S) (h6 : x6 ∈ S)
    (lt1 : x1 < x2) (lt2 : x2 < x3) (lt3 : x3 < x4)
    (lt4 : x4 < x5) (lt5 : x5 < x6) :
    altSum6 x1 x2 x3 x4 x5 x6 ≠ 0 := by
  have h_mem : [x1, x2, x3, x4, x5, x6] ∈ S.sublists.filter (fun l => l.length == 6) := by
    rw [List.mem_filter, List.mem_sublists]
    refine ⟨⟨List.subsequence_of_subset (by simp [h1, h2, h3, h4, h5, h6]), by simp⟩, by simp⟩
  have h_all := List.all_eq_true.mp allCheck_true [x1, x2, x3, x4, x5, x6] h_mem
  dsimp [checkTuple, altSum6] at h_all
  rw [if_pos (by exact ⟨lt1, ⟨lt2, ⟨lt3, ⟨lt4, lt5⟩⟩⟩⟩)] at h_all
  exact h_all