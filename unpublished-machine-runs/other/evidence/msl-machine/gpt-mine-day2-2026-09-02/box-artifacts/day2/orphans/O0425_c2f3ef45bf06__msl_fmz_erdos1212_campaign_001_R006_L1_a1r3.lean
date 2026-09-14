import Mathlib

set_option autoImplicit false



def Valid (p : ℕ × ℕ) : Prop :=
  1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1 ∧ (¬ p.1.Prime ∨ ¬ p.2.Prime)

def Adj (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)) ∨
  (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1))

theorem msl_fmz_erdos1212_campaign_001_R006_L1_a1r3  : ∀ q : ℕ × ℕ, Adj (2, 9) q → ¬ Valid q := by
  intro q hq
  rcases q with ⟨x, y⟩
  unfold Adj at hq
  unfold Valid
  intro hv
  rcases hv with ⟨hx, hy, hg, hprime⟩
  rcases hq with hq | hq
  · rcases hq with ⟨hxy, hy'⟩
    have hx' : x = 2 := by simpa using hxy
    subst x
    rcases hy' with hy' | hy'
    · have : y = 8 := by omega
      subst y
      norm_num at hg
    · have : y = 10 := by omega
      subst y
      norm_num at hg
  · rcases hq with ⟨hy', hx'⟩
    have hy'' : y = 9 := by simpa using hy'
    subst y
    rcases hx' with hx' | hx'
    · have : x = 1 := by omega
      subst x
      omega
    · have : x = 3 := by omega
      subst x
      norm_num at hg

-- axiom footprint
#print axioms Valid
#print axioms Adj
#print axioms msl_fmz_erdos1212_campaign_001_R006_L1_a1r3
