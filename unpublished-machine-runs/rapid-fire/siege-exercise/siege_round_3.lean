import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Decide

def S_list : List ℤ := [1, 3, 9, 27, 81, 243, 729, 2187]

def checkTuple (xs : List ℤ) : Bool :=
  match xs with
  | [x1, x2, x3, x4, x5, x6] =>
    if x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 then
      1 * x1 - 5 * x2 + 10 * x3 - 10 * x4 + 5 * x5 - 1 * x6 ≠ 0
    else
      true
  | _ => true

def allCheck : Bool :=
  (S_list.sublists.filter (fun l => l.length == 6)).all checkTuple

theorem allCheck_eq_true : allCheck = true := by
  native_decide

theorem S_avoids_fifth_diff :
    ∀ x1 x2 x3 x4 x5 x6 : ℤ,
      x1 ∈ S_list → x2 ∈ S_list → x3 ∈ S_list →
      x4 ∈ S_list → x5 ∈ S_list → x6 ∈ S_list →
      x1 < x2 → x2 < x3 → x3 < x4 → x4 < x5 → x5 < x6 →
      1 * x1 - 5 * x2 + 10 * x3 - 10 * x4 + 5 * x5 - 1 * x6 ≠ 0 := by
  intros x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6 lt1 lt2 lt3 lt4 lt5
  have h_mem : [x1, x2, x3, x4, x5, x6] ∈ S_list.sublists.filter (fun l => l.length == 6) := by
    rw [List.mem_filter, List.mem_sublists]
    refine ⟨⟨List.subsequence_of_subset (by simp [h1, h2, h3, h4, h5, h6]), by simp⟩, by simp⟩
  have h_all := List.all_eq_true.mp allCheck_eq_true [x1, x2, x3, x4, x5, x6] h_mem
  unfold checkTuple at h_all
  simp only [lt1, lt2, lt3, lt4, lt5, and_self, if_true] at h_all
  exact h_all