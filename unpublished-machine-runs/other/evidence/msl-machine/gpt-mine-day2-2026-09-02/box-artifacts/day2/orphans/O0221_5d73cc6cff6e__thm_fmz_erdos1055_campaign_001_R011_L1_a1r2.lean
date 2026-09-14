import Mathlib

set_option autoImplicit false



def MatchesAnchors (f : ℕ → ℕ) : Prop :=
  f 13 = 2 ∧ f 37 = 3 ∧ f 73 = 4

def TotalLabelingOnPrimes400 (f : ℕ → ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ 400 → ∃ n : ℕ, f q = n

def L1Statement : Prop :=
  ∃ f₁ f₂ : ℕ → ℕ,
    TotalLabelingOnPrimes400 f₁ ∧
    TotalLabelingOnPrimes400 f₂ ∧
    MatchesAnchors f₁ ∧
    MatchesAnchors f₂ ∧
    f₁ 2 ≠ f₂ 2

theorem msl_fmz_erdos1055_campaign_001_R011_L1_a1r2  : L1Statement := by
  let f₁ : ℕ → ℕ := fun q => if q = 13 then 2 else if q = 37 then 3 else if q = 73 then 4 else 0
  let f₂ : ℕ → ℕ := fun q => if q = 13 then 2 else if q = 37 then 3 else if q = 73 then 4 else 500 + q
  refine ⟨f₁, f₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hq400
    exact ⟨f₁ q, rfl⟩
  · intro q hq hq400
    exact ⟨f₂ q, rfl⟩
  · constructor
    · simp [MatchesAnchors, f₁]
    · constructor
      · simp [MatchesAnchors, f₁]
      · simp [MatchesAnchors, f₁]
  · constructor
    · simp [MatchesAnchors, f₂]
    · constructor
      · simp [MatchesAnchors, f₂]
      · simp [MatchesAnchors, f₂]
  · simp [f₁, f₂]

-- axiom footprint
#print axioms MatchesAnchors
#print axioms TotalLabelingOnPrimes400
#print axioms L1Statement
#print axioms msl_fmz_erdos1055_campaign_001_R011_L1_a1r2
