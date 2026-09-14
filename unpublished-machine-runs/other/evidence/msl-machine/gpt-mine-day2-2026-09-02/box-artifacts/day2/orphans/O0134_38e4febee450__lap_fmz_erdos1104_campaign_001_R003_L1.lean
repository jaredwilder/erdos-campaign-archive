import Mathlib

set_option autoImplicit false



def fBound (n : ℕ) (c1 : ℝ) : Prop := f n ≥ c1 * Real.sqrt (n / Real.log n)
-- f is the campaign's standing definition: sSup of chromatic numbers over triangle-free
-- graphs on Fin n. The reduction lemma used inside the proof:
-- LemmaDel : ∀ n N, n ≤ N → ∀ G : SimpleGraph (Fin N), G.TriangleFree →
--   ∃ H : SimpleGraph (Fin n), H.TriangleFree ∧ H.chromaticNumber ≥ N / G.independenceNumber
-- (vertex deletion: induce on any n-subset; triangle-free hereditary; χ(H) ≥ n/α ≥ N/α).

axiom PublishedTheorem_Kim1995 :
  ∃ (c : ℝ), 0 < c ∧ ∃ (t₀ : ℕ), ∀ t ≥ t₀, ∃ (N : ℕ), N ≥ 2 * t^2 ∧ ∃ (G : SimpleGraph (Fin N)), G.TriangleFree ∧ G.independenceNumber < 2 * t

theorem msl_fmz_erdos1104_campaign_001_R003_L1  : theorem R003_L1_lower_half : ∃ (c1 : ℝ), 0 < c1 ∧ ∀ᶠ n in Filter.atTop, f n ≥ c1 * Real.sqrt (n / Real.log n) := obtain ⟨c, hc, t₀, hK⟩ := PublishedTheorem_Kim1995
refine ⟨Real.sqrt (c/4), by positivity, ?_⟩
Filter.eventually_atTop.mpr ⟨n₀, fun n hn => ?_⟩
-- For n ≥ n₀ set t := ⌈√(n·log n / (2c))⌉, so t ≥ t₀ and 2·t² ≥ n·log n / c, hence
-- c·2t²/log n ≥ n i.e. N := c·t²/log t ≥ n for n large (log t ~ log n bookkeeping, n ≥ n₀).
obtain ⟨N, hN, G, hGfree, hGα⟩ := hK t ht
obtain ⟨H, hHfree, hHχ⟩ := LemmaDel n N (le_of_lt hNn) G hGfree hGα
-- f n ≥ χ(H) ≥ N / α(G) > N / (2t) ≥ c·t²/(2·t·log n) = c·t/(2·log n) ≥ √(c/4)·√(n/log n).
exact le_trans (le_f_sup hHfree) (by linarith [hHχ, hN, hGα, ht, hn])

-- axiom footprint
#print axioms fBound
#print axioms msl_fmz_erdos1104_campaign_001_R003_L1
