import Mathlib

/-!
Erdős 885: an independently checked `k = 4` witness recorded by Bremner.

For `N = a*b`, the displayed equality `a-b=d` says directly that the
factor-difference `d` belongs to `D(N)`.  Thus the sixteen checked factor
pairs below show that all four displayed `N`s have the same four members of
their factor-difference sets.  This is a finite known case, not a proof of
the open all-`k` question.
-/

def HasFactorGap (N d : ℕ) : Prop :=
  ∃ a b : ℕ, a * b = N ∧ a - b = d

theorem erdos885_bremner_k4_witness :
    26128575 < 291722431 ∧ 291722431 < 561117375 ∧ 561117375 < 713526975 ∧
    HasFactorGap 26128575 126 ∧ HasFactorGap 26128575 16110 ∧
    HasFactorGap 26128575 33390 ∧ HasFactorGap 26128575 75390 ∧
    HasFactorGap 291722431 126 ∧ HasFactorGap 291722431 16110 ∧
    HasFactorGap 291722431 33390 ∧ HasFactorGap 291722431 75390 ∧
    HasFactorGap 561117375 126 ∧ HasFactorGap 561117375 16110 ∧
    HasFactorGap 561117375 33390 ∧ HasFactorGap 561117375 75390 ∧
    HasFactorGap 713526975 126 ∧ HasFactorGap 713526975 16110 ∧
    HasFactorGap 713526975 33390 ∧ HasFactorGap 713526975 75390 := by
  refine ⟨by norm_num, by norm_num, by norm_num,
    ⟨5175, 5049, by norm_num, by norm_num⟩,
    ⟨17595, 1485, by norm_num, by norm_num⟩,
    ⟨34155, 765, by norm_num, by norm_num⟩,
    ⟨75735, 345, by norm_num, by norm_num⟩,
    ⟨17143, 17017, by norm_num, by norm_num⟩,
    ⟨26939, 10829, by norm_num, by norm_num⟩,
    ⟨40579, 7189, by norm_num, by norm_num⟩,
    ⟨79079, 3689, by norm_num, by norm_num⟩,
    ⟨23751, 23625, by norm_num, by norm_num⟩,
    ⟨33075, 16965, by norm_num, by norm_num⟩,
    ⟨45675, 12285, by norm_num, by norm_num⟩,
    ⟨82215, 6825, by norm_num, by norm_num⟩,
    ⟨26775, 26649, by norm_num, by norm_num⟩,
    ⟨35955, 19845, by norm_num, by norm_num⟩,
    ⟨48195, 14805, by norm_num, by norm_num⟩,
    ⟨83895, 8505, by norm_num, by norm_num⟩⟩
