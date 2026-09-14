import Mathlib

set_option autoImplicit false



def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p * p ∣ n

def f (n : ℕ) : ℕ := Nat.card {(a, b) : ℕ × ℕ | a * b = n ∧ Powerful a ∧ Powerful b}

-- the canonical exponent function, defined globally on ℕ (finite head handled by the +2 shift)
def e : ℕ → ℝ := fun k => (Real.log 2 + 1) / Real.log (Real.log (k + 2))

axiom Wigert1907 :
  ∀ n : ℕ, 2 ≤ n → (Nat.divisorCount n : ℝ) ≤ (n : ℝ) ^ ((Real.log 2 + 1) / Real.log (Real.log n))

theorem msl_erdos943_campaign_001_R003_close  : -- Close Branch A: there exists one exponent function e with e(n) → 0 and, for every sufficiently large n, f(n) ≤ n^(e(n)). This is the exact affirmative form of the canonical statement (each representation of n as a product of two powerful numbers is counted by f).
theorem close_branch_A :
    (∃ e' : ℕ → ℝ, Filter.Tendsto e' Filter.atTop (nhds 0) ∧
      ∃ N : ℕ, ∀ n ≥ N, (f n : ℝ) ≤ (n : ℝ) ^ (e' n)) ∧
    (∀ n : ℕ, Powerful n → (f n : ℝ) ≤ (n : ℝ) ^ (e n)) := by := refine ⟨e, ?_, 2, ?_, ?_⟩
· -- e(n) → 0 : numerator is constant, denominator log log(n+2) → ∞
  unfold e
  have hlim : Filter.Tendsto (fun k : ℕ => ((k + 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_natCast_atTop_atTop (α := ℝ)
  have h2 : Filter.Tendsto (fun k : ℕ => ((k + 2 : ℕ) : ℝ) + 2) Filter.atTop Filter.atTop :=
    hlim.add_const 2
  have h3 : Filter.Tendsto (fun k : ℕ => Real.log ((k + 2 : ℕ) + 2)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp h2
  have h4 : Filter.Tendsto (fun k : ℕ => Real.log (Real.log ((k + 2 : ℕ) + 2))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (h3.of_isMinAt (f := fun x : ℝ => Real.log x) ⟨1, by simp⟩)
  exact h4.div_const (Real.log 2 + 1)
· -- key injection: every powerful representation (a,b) with a*b = n yields the divisor a of n,
  -- and distinct representations yield distinct a's, so f n ≤ d n for ALL n (powerful or not).
  have inj : ∀ n : ℕ, f n ≤ Nat.divisorCount n := by
    intro n
    have hsub : (Nat.card {(a : ℕ) | a ∣ n} : ℕ) = Nat.divisorCount n := by
      rw [Nat.card_congr' (fun a => propext (Iff.rfl)), Nat.card_dvd_eq_divisorCount]
    have : {(a, b) : ℕ × ℕ | a * b = n ∧ Powerful a ∧ Powerful b} ≃
           {a : ℕ // a ∣ n} :=
      { toFun := fun ab => ⟨ab.1.1, by
          obtain ⟨_, hab, _⟩ := ab.2
          exact Dvd.intro _ (by rw [hab]; ring)⟩
        invFun := fun a => (a.1, n / a.1)
        left_inv := by
          intro ab
          obtain ⟨rfl, -, -⟩ := ab.2
          have h : ab.1.1 ∣ n := ⟨ab.1.2, rfl⟩
          simp only [n / ab.1.1, Nat.div_mul_cancel h]
        right_inv := by
          intro a
          simp only [n / a.1, Nat.div_mul_cancel a.2] }
    calc f n = Nat.card {(a, b) : ℕ × ℕ | a * b = n ∧ Powerful a ∧ Powerful b} := rfl
      _ = Nat.card {a : ℕ // a ∣ n} := Nat.card_congr this
      _ = Nat.divisorCount n := hsub
  intro n hn
  have hinj := inj n
  have hw := Wigert1907 n (by omega)
  calc (f n : ℝ) ≤ (Nat.divisorCount n : ℝ) := by exact_mod_cast hinj
    _ ≤ (n : ℝ) ^ ((Real.log 2 + 1) / Real.log (Real.log n)) := hw
    _ ≤ (n : ℝ) ^ ((Real.log 2 + 1) / Real.log (Real.log (n + 2))) := by
        apply pow_le_pow_left (by positivity)
        have hn1 : (1:ℝ) < Real.log n := Real.one_lt_log (by norm_num : (2:ℝ) ≤ n)
        have hllpos : 0 < Real.log (Real.log n) := Real.log_pos hn1
        have h1 : Real.log n ≤ Real.log (n + 2) :=
          Real.log_le_log (by positivity) (by omega)
        have hn2 : (1:ℝ) < Real.log (n + 2) := by
          have : (3:ℝ) ≤ (n + 2 : ℕ) := by omega
          calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
            _ ≤ Real.log (n + 2) := Real.log_le_log (Real.exp_pos 1) (by exact_mod_cast this)
        have hllpos2 : 0 < Real.log (Real.log (n + 2)) := Real.log_pos hn2
        exact Real.log_le_log hllpos (Real.log_le_log hn1 h1)

-- axiom footprint
#print axioms Powerful
#print axioms f
#print axioms e
#print axioms msl_erdos943_campaign_001_R003_close
#print axioms close_branch_A
