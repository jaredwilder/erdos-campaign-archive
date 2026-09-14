import Mathlib

set_option autoImplicit false

-- Erdos 155 RESCUE (fusion queue rank 2, 2026-09-02): verbatim copy of the failed
-- formalizer artifact thm_fmz-erdos155-campaign-001-R005-L1.lean with ONE repair:
-- the duplicate `import Mathlib` after set_option (illegal placement) is removed.
-- No mathematical content changed. Original receipt: KERNEL_FAILED on the import line.


namespace R005L1

/-- Sidon (diagonal-inclusive, unordered pairs): all sums a+b with a,b ∈ s
are distinct up to swapping of the two summands. -/
def IsSidon (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

open scoped Classical

/-- F(N) = size of the largest Sidon subset of {1,…,N}, defined by exhaustive
filter over the powerset (mirrors the contract's maxSidonSubsetCard encoding). -/
noncomputable def F (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun s => IsSidon s)).sup Finset.card

/-- Any Sidon subset of Icc 1 N has cardinality at most F N. -/
theorem le_F {N : ℕ} {s : Finset ℕ} (hsub : s ⊆ Finset.Icc 1 N) (hS : IsSidon s) :
    s.card ≤ F N := by
  have hmem : s ∈ (Finset.Icc 1 N).powerset.filter (fun t => IsSidon t) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hS⟩
  exact Finset.le_sup hmem

end R005L1

theorem msl_fmz_erdos155_campaign_001_R005_L1  : ∀ N : ℕ, R005L1.F (N + 1) ≤ R005L1.F N + 1 := by
  intro N
  refine Finset.sup_le (fun s hs => ?_)
  obtain ⟨hpow, hS⟩ := Finset.mem_filter.mp hs
  obtain ⟨h1, -⟩ := Finset.mem_powerset.mp hpow
  -- h1 : s ⊆ Icc 1 (N+1)
  by_cases hmemN : N + 1 ∈ s
  · -- Case 1: s contains N+1; delete it. The deletion is a Sidon subset of Icc 1 N
    -- and costs exactly one element.
    have hdel : s.erase (N + 1) ⊆ Finset.Icc 1 N := by
      intro x hx
      have hxin : x ∈ s := Finset.mem_of_mem_erase hx
      have hpair := Finset.mem_Icc.mp (h1 hxin)
      have hge := hpair.1
      have hle := hpair.2
      have hxne : x ≠ N + 1 := (Finset.mem_erase.mp hx).1
      exact Finset.mem_Icc.mpr ⟨hge, by omega⟩
    have hSid : R005L1.IsSidon (s.erase (N + 1)) := by
      intro a ha b hb c hc d hd hsum
      exact hS a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
        c (Finset.mem_of_mem_erase hc) d (Finset.mem_of_mem_erase hd) hsum
    have hbound := R005L1.le_F hdel hSid
    have hcard : s.card = (s.erase (N + 1)).card + 1 := by
      rw [Finset.card_erase_of_mem hmemN]; omega
    omega
  · -- Case 2: s avoids N+1; then s is already a Sidon subset of Icc 1 N.
    have hdel : s ⊆ Finset.Icc 1 N := by
      intro x hx
      have hpair := Finset.mem_Icc.mp (h1 hx)
      have hge := hpair.1
      have hle := hpair.2
      have hxne : x ≠ N + 1 := fun h => hmemN (h ▸ hx)
      exact Finset.mem_Icc.mpr ⟨hge, by omega⟩
    have hbound := R005L1.le_F hdel hS
    omega

-- axiom footprint
#print axioms R005L1.IsSidon
#print axioms R005L1.F
#print axioms R005L1.le_F
#print axioms msl_fmz_erdos155_campaign_001_R005_L1
