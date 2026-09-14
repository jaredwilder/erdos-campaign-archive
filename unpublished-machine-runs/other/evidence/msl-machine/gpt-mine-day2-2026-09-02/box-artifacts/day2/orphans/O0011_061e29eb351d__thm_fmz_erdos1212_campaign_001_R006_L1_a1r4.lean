import Mathlib

set_option autoImplicit false



def Valid (p : ℕ × ℕ) : Prop :=
  1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1 ∧
    (¬ p.1.Prime ∨ ¬ p.2.Prime)

def Adj (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)) ∨
  (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1))

theorem msl_fmz_erdos1212_campaign_001_R006_L1_a1r4  : ∀ q : ℕ × ℕ, Adj (2, 9) q → ¬ Valid q := by
  intro q hq hvalid
  rcases q with ⟨x, y⟩
  simp only [Adj, Prod.fst, Prod.snd] at hq
  simp only [Valid, Prod.fst, Prod.snd] at hvalid
  rcases hvalid with ⟨hx, hy, hg, hprime⟩
  rcases hq with ⟨hxy, hstep⟩ | ⟨hyx, hstep⟩
  · have hx2 : x = 2 := by omega
    rcases hstep with h8 | h10
    · have hy8 : y = 8 := by omega
      subst x
      subst y
      norm_num at hg
    · have hy10 : y = 10 := by omega
      subst x
      subst y
      norm_num at hg
  · have hy9 : y = 9 := by omega
    rcases hstep with h1 | h3
    · have hx1 : x = 1 := by omega
      subst x
      subst y
      omega
    · have hx3 : x = 3 := by omega
      subst x
      subst y
      norm_num at hg

-- axiom footprint
#print axioms Valid
#print axioms Adj
#print axioms msl_fmz_erdos1212_campaign_001_R006_L1_a1r4
