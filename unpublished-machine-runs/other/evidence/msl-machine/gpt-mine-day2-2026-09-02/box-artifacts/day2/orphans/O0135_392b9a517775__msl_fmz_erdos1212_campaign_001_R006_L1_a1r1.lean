import Mathlib

set_option autoImplicit false



def Valid (p : ℕ × ℕ) : Prop := 1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1 ∧ (¬ p.1.Prime ∨ ¬ p.2.Prime)

def Adj (p q : ℕ × ℕ) : Prop := (p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)) ∨ (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1))

theorem msl_fmz_erdos1212_campaign_001_R006_L1_a1r1  : ∀ q : ℕ × ℕ, Adj (2, 9) q → ¬ Valid q := by
  intro q hAdj hValid
  rcases q with ⟨x, y⟩
  unfold Adj at hAdj
  unfold Valid at hValid
  rcases hValid with ⟨hx, hy, hg, hcomp⟩
  rcases hAdj with hAdj | hAdj
  · rcases hAdj with ⟨h2, hY⟩
    rcases hY with hY | hY
    · have hy8 : y = 8 := by omega
      subst x
      subst y
      norm_num at hg
    · have hy10 : y = 10 := by omega
      subst x
      subst y
      norm_num at hg
  · rcases hAdj with ⟨h9, hX⟩
    rcases hX with hX | hX
    · have hx1 : x = 1 := by omega
      subst x
      omega
    · have hx3 : x = 3 := by omega
      subst x
      subst y
      norm_num at hg

-- axiom footprint
#print axioms Valid
#print axioms Adj
#print axioms msl_fmz_erdos1212_campaign_001_R006_L1_a1r1
