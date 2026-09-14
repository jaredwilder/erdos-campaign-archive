import Mathlib

set_option autoImplicit false



-- D(n,3,2): max number of blocks in a 2-(n,3,1) packing
noncomputable def D (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ S : Finset (Finset (Fin n)),
    (∀ b ∈ S, b.card = 3) ∧ S.card = m ∧
    (∀ p : Fin n × Fin n, ({p.1, p.2} : Finset (Fin n)).card = 2 →
      (S.filter (fun b => p.1 ∈ b ∧ p.2 ∈ b)).card ≤ 1)}

-- e(n,2): max edges in a graph on n vertices where every edge lies in a triangle
noncomputable def e (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), G.edgeFinset.card = m ∧
    (∀ e' ∈ G.edgeFinset, ∃ w x y,
      G.Adj w x ∧ G.Adj x y ∧ G.Adj y w ∧ (w = e'.1 ∨ x = e'.1 ∨ y = e'.1))}

-- Route R002's PROVED identity, taken here as a hypothesis (not re-proved)
hE : ∀ n, e n = D n

axiom PublishedTheorem_Rodl1985 :
  ∀ ε > (0:ℚ), ∃ N : ℕ, ∀ n ≥ N, |(D n : ℚ) - n*(n-1)/6| < ε * n*(n-1)

theorem msl_fmz_erdos600_campaign_001_R002_L1  : theorem L1_baseline (hE : ∀ n, e n = D n) :
    Filter.Tendsto (fun n => ((e n : ℚ)) / (n * (n - 1))) Filter.atTop (nhds (1/6)) := have h1 := fun n => hE n
have key : Filter.Tendsto (fun n => ((D n : ℚ)) / (n * (n - 1))) Filter.atTop (nhds (1/6)) := by
  rw [Asymptotics.tendsto_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := PublishedTheorem_Rodl1985 (ε/2) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  -- from |D n - n(n-1)/6| < (ε/2)·n(n-1), for n ≥ N ≥ 2 so n(n-1) > 0:
  have hpos : (0:ℚ) < n * (n - 1) := by have : n ≥ 2 := by omega; nlinarith
  have habs : |((D n : ℚ)) / (n * (n - 1)) - 1/6| < ε := by
    have : ((D n : ℚ)) / (n * (n - 1)) - 1/6
        = ((D n : ℚ) - n*(n-1)/6) / (n * (n - 1)) := by field_simp
    rw [this, abs_div hpos.le (by linarith)]
    rw [abs_sub_comm]
    calc |(D n : ℚ) - n*(n-1)/6| / (n * (n - 1)) < (ε/2) * n*(n-1) / (n * (n-1)) := by
            apply div_lt_div _ hpos.le; exact h
      _ = ε/2 := by field_simp
      _ < ε := by linarith
  exact habs
exact h1 ▸ key

-- axiom footprint
#print axioms D
#print axioms e
#print axioms msl_fmz_erdos600_campaign_001_R002_L1
