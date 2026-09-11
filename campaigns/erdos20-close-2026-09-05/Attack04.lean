/-
Erdős Problem 20 — the Sunflower Conjecture.

ATTACK 04:
  * `lower_of_witness` — a reusable engine: ANY explicit sunflower-free family is
    a lower bound on `f`.  (Attack03's `erdos_rado_lower` is one instance; future
    improved constructions plug straight in.)
  * `f_two : f n 2 = 2` — an EXACT value, against the Erdős–Rado bound `n! + 1`.
    Evidence that the `n!` is not tight; the open problem lives at large `k`.
  * `const_lower` — any constant `c` witnessing Erdős' `f n k < c^n` must satisfy
    `k ≤ c`.  A constraint on the answer to the open question itself.
-/
import Mathlib
import Attack01
import Attack02
import Attack03

namespace Erdos20Lower

open Erdos20Corpus

/-- The defining set of `f n k`. -/
def Tset (n k : ℕ) : Set ℕ :=
  {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ f ∈ F, f.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

lemma f_eq_sInf (n k : ℕ) : f n k = sInf (Tset n k) := rfl

lemma Tset_nonempty (n k : ℕ) (hn : 0 < n) : (Tset n k).Nonempty :=
  ⟨(k - 1) ^ n * n.factorial + 1, erdos_rado_mem n k hn⟩

/-- **Lower-bound engine.** An explicit `k`-sunflower-free `n`-uniform family of size
`≥ m` forces `m < f n k`. -/
theorem lower_of_witness {α : Type} (n k m : ℕ) (hn : 0 < n) (F : Set (Set α))
    (huni : ∀ A ∈ F, A.ncard = n) (hcard : m ≤ F.ncard)
    (hfree : ∀ S ⊆ F, S.ncard = k → ¬ IsSunflower S) :
    m < f n k := by
  by_contra hcon
  push_neg at hcon
  have hmem : sInf (Tset n k) ∈ Tset n k := Nat.sInf_mem (Tset_nonempty n k hn)
  rw [f_eq_sInf] at hcon
  obtain ⟨S, hSsub, hScard, hSun⟩ :=
    hmem F ⟨huni, le_trans hcon hcard⟩
  exact hfree S hSsub hScard hSun

/-! ### The exact value at `k = 2` -/

/-- Any two distinct sets already form a `2`-sunflower, so `f n 2 ≤ 2`. -/
theorem f_two_le (n : ℕ) : f n 2 ≤ 2 := by
  apply Nat.sInf_le
  intro α F hFF
  obtain ⟨_huni, hcard⟩ := hFF
  have hFfin : F.Finite := by
    by_contra h
    have h0 := Set.Infinite.ncard h
    omega
  have hex : ∃ A ∈ F, ∃ B ∈ F, A ≠ B := by
    by_contra hcon
    push_neg at hcon
    have h1 : F.ncard ≤ 1 := (Set.ncard_le_one hFfin).mpr (fun a ha b hb => hcon a ha b hb)
    omega
  obtain ⟨A, hA, B, hB, hAB⟩ := hex
  refine ⟨{A, B}, ?_, Set.ncard_pair hAB, ⟨A ∩ B, ?_⟩⟩
  · rintro X (rfl | rfl)
    · exact hA
    · exact hB
  · rintro X (rfl | rfl) Y (rfl | rfl) hXY
    · exact absurd rfl hXY
    · rfl
    · exact Set.inter_comm _ _
    · exact absurd rfl hXY

/-- **`f n 2 = 2` exactly** — for every `n > 0`.
Compare the Erdős–Rado bound at `k = 2`, which only gives `f n 2 ≤ n! + 1`. -/
theorem f_two (n : ℕ) (hn : 0 < n) : f n 2 = 2 := by
  have hu := f_two_le n
  have hl : 1 < f n 2 := by
    refine lower_of_witness (α := Fin n) n 2 1 hn {(Set.univ : Set (Fin n))} ?_ ?_ ?_
    · rintro A rfl
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    · rw [Set.ncard_singleton]
    · intro S hS hScard _
      have h1 : S.ncard ≤ ({(Set.univ : Set (Fin n))} : Set (Set (Fin n))).ncard :=
        Set.ncard_le_ncard hS (Set.finite_singleton _)
      rw [Set.ncard_singleton, hScard] at h1
      omega
  omega

/-! ### A constraint on the answer to the OPEN question -/

/--
Erdős asks whether `f n k < c_k ^ n` for some constant `c_k`.  Whatever the answer,
the lower bound forces **`k ≤ c_k`**: the constant can never be smaller than `k`.
-/
theorem const_lower (k c : ℕ) (hk : 2 ≤ k)
    (hc : ∀ n, 0 < n → f n k < c ^ n) : k ≤ c := by
  have h1 := erdos_rado_lower 1 k (by norm_num) hk
  have h2 := hc 1 (by norm_num)
  rw [pow_one] at h1 h2
  omega

end Erdos20Lower

#print axioms Erdos20Lower.lower_of_witness
#print axioms Erdos20Lower.f_two_le
#print axioms Erdos20Lower.f_two
#print axioms Erdos20Lower.const_lower
