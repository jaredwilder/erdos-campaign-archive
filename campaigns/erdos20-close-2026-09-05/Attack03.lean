/-
Erdős Problem 20 — the Sunflower Conjecture.

ATTACK 03: the matching LOWER bound.  The Erdős–Rado product construction
(all transversals of `n` disjoint blocks of size `k-1`) is a `k`-sunflower-free
`n`-uniform family of size `(k-1)^n`, hence

    (k-1)^n  <  f n k  ≤  (k-1)^n * n! + 1.

This pins the exact content of the open problem: the lower bound already has the
shape `c_k^n` with `c_k = k-1`, so Erdős' question "is `f(n,k) < c_k^n`?" is
precisely the question of whether the `n!` in the Erdős–Rado upper bound can be
removed.  Corollary: `f 1 k = k` exactly.

`f`, `IsSunflower` are the corpus objects (Attack02).
-/
import Mathlib
import Attack01
import Attack02

namespace Erdos20Lower

open Erdos20Corpus

/-! ### The Erdős–Rado product construction -/

/-- The transversal of the `n` blocks `{i} × Fin m` selected by `a`. -/
def Aset {n m : ℕ} (a : Fin n → Fin m) : Set (Fin n × Fin m) := {p | p.2 = a p.1}

lemma Aset_eq_image {n m : ℕ} (a : Fin n → Fin m) :
    Aset a = (fun i => (i, a i)) '' Set.univ := by
  ext p
  simp only [Aset, Set.mem_setOf_eq, Set.image_univ, Set.mem_range]
  constructor
  · intro h
    exact ⟨p.1, by rw [← h]⟩
  · rintro ⟨i, rfl⟩
    rfl

lemma Aset_injOn_pt {n m : ℕ} (a : Fin n → Fin m) :
    Set.InjOn (fun i => (i, a i)) (Set.univ : Set (Fin n)) := by
  intro i _ j _ h
  exact congrArg Prod.fst h

lemma Aset_ncard {n m : ℕ} (a : Fin n → Fin m) : (Aset a).ncard = n := by
  rw [Aset_eq_image, (Aset_injOn_pt a).ncard_image, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

lemma Aset_injective {n m : ℕ} : Function.Injective (Aset (n := n) (m := m)) := by
  intro a b h
  funext i
  have hmem : ((i, a i) : Fin n × Fin m) ∈ Aset b := by rw [← h]; rfl
  exact hmem

/-- The family of ALL transversals: `(k-1)^n` sets of size `n`, `k`-sunflower-free. -/
def Fam (n m : ℕ) : Set (Set (Fin n × Fin m)) := Set.range (Aset (n := n) (m := m))

lemma Fam_uniform {n m : ℕ} : ∀ A ∈ Fam n m, A.ncard = n := by
  rintro A ⟨a, rfl⟩
  exact Aset_ncard a

lemma Fam_ncard (n m : ℕ) : (Fam n m).ncard = m ^ n := by
  rw [Fam, ← Set.image_univ, Set.InjOn.ncard_image (Aset_injective.injOn), Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-! ### It is sunflower-free -/

theorem Fam_no_sunflower {n k : ℕ} (hk : 2 ≤ k)
    (S : Set (Set (Fin n × Fin (k - 1))))
    (hS : S ⊆ Fam n (k - 1)) (hScard : S.ncard = k) : ¬ IsSunflower S := by
  rintro ⟨C, hC⟩
  classical
  haveI : NeZero (k - 1) := ⟨by omega⟩
  have hSfin : S.Finite := Set.Finite.subset (Set.finite_range _) hS
  have hrep : ∀ X ∈ S, ∃ a : Fin n → Fin (k - 1), Aset a = X := fun X hX => hS hX
  choose! g hg using hrep
  have hgmem : ∀ X ∈ S, ∀ p : Fin n × Fin (k - 1), (p ∈ X ↔ p.2 = g X p.1) := by
    intro X hX p
    constructor
    · intro hp
      have h1 : p ∈ Aset (g X) := by rw [hg X hX]; exact hp
      exact h1
    · intro hp
      have h1 : p ∈ Aset (g X) := hp
      rw [hg X hX] at h1
      exact h1
  -- agreement of two representatives at coordinate `i` ⟺ that point lies in the kernel
  have key : ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → ∀ i : Fin n,
      (g X i = g Y i ↔ ((i, g X i) : Fin n × Fin (k - 1)) ∈ C) := by
    intro X hX Y hY hXY i
    have hCXY : X ∩ Y = C := hC hX hY hXY
    constructor
    · intro h
      rw [← hCXY]
      exact ⟨(hgmem X hX _).mpr rfl, (hgmem Y hY _).mpr h⟩
    · intro h
      rw [← hCXY] at h
      exact (hgmem Y hY _).mp h.2
  -- two distinct members exist since `k ≥ 2`
  have hex2 : ∃ X ∈ S, ∃ Y ∈ S, X ≠ Y := by
    by_contra hcon
    push_neg at hcon
    have h1 : S.ncard ≤ 1 := (Set.ncard_le_one hSfin).mpr (fun a ha b hb => hcon a ha b hb)
    omega
  obtain ⟨X₀, hX₀, X₁, hX₁, hne⟩ := hex2
  have hgne : g X₀ ≠ g X₁ := by
    intro h
    exact hne (by rw [← hg X₀ hX₀, ← hg X₁ hX₁, h])
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hgne
  -- at that coordinate the k representatives are pairwise distinct: k ≤ k-1
  have hinj : Set.InjOn (fun X => g X i) S := by
    intro X hX Y hY hXY
    by_contra hXneY
    have hmem : ((i, g X i) : Fin n × Fin (k - 1)) ∈ C := (key X hX Y hY hXneY i).mp hXY
    have hC01 : X₀ ∩ X₁ = C := hC hX₀ hX₁ hne
    rw [← hC01] at hmem
    have e0 : g X i = g X₀ i := (hgmem X₀ hX₀ _).mp hmem.1
    have e1 : g X i = g X₁ i := (hgmem X₁ hX₁ _).mp hmem.2
    exact hi (by rw [← e0, ← e1])
  have hle : S.ncard ≤ (Set.univ : Set (Fin (k - 1))).ncard :=
    Set.ncard_le_ncard_of_injOn (fun X => g X i) (fun X _ => Set.mem_univ _) hinj Set.finite_univ
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, hScard] at hle
  omega

/-! ### The lower bound on `f` -/

/-- **Erdős–Rado lower bound.** `(k-1)^n < f n k`. -/
theorem erdos_rado_lower (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) : (k - 1) ^ n < f n k := by
  set T : Set ℕ := {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ f ∈ F, f.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S} with hT
  have hfT : f n k = sInf T := rfl
  have hTne : T.Nonempty := ⟨(k - 1) ^ n * n.factorial + 1, erdos_rado_mem n k hn⟩
  have hmem : sInf T ∈ T := Nat.sInf_mem hTne
  by_contra hcon
  push_neg at hcon
  rw [hfT] at hcon
  have hcard : sInf T ≤ (Fam n (k - 1)).ncard := by rw [Fam_ncard]; exact hcon
  obtain ⟨S, hSsub, hScard, hSun⟩ :=
    hmem (Fam n (k - 1)) ⟨Fam_uniform, hcard⟩
  exact Fam_no_sunflower hk S hSsub hScard hSun

/-- **The sandwich.** `(k-1)^n < f n k ≤ (k-1)^n * n! + 1`. -/
theorem erdos_rado_sandwich (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    (k - 1) ^ n < f n k ∧ f n k ≤ (k - 1) ^ n * n.factorial + 1 :=
  ⟨erdos_rado_lower n k hn hk, erdos_rado_bound n k hn hk⟩

/-- **Exact value at `n = 1`:** `f 1 k = k`. -/
theorem f_one (k : ℕ) (hk : 2 ≤ k) : f 1 k = k := by
  have hu := erdos_rado_bound 1 k (by norm_num) hk
  have hl := erdos_rado_lower 1 k (by norm_num) hk
  rw [pow_one] at hu hl
  rw [Nat.factorial_one, mul_one] at hu
  omega

end Erdos20Lower

#print axioms Erdos20Lower.Fam_no_sunflower
#print axioms Erdos20Lower.erdos_rado_lower
#print axioms Erdos20Lower.erdos_rado_sandwich
#print axioms Erdos20Lower.f_one
