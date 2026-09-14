import Mathlib

set_option maxRecDepth 400000

/-! # JSPACE SHOT 19 — the signature multiplicity bound (4), in the kernel. -/

namespace JSpaceShot19

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

def Dset (T : Tournament V) (A : Finset V) : Finset V :=
  univ.filter (fun v => ∀ a ∈ A, T.beats v a)

/-- Signature of `u` against `Av`. -/
def sig (T : Tournament V) (Av : Finset V) (u : V) : Finset V :=
  Av.filter (fun a => T.beats a u)

/-- The signature class of `P`. -/
def sigClass (T : Tournament V) (Av : Finset V) (P : Finset V) : Finset V :=
  univ.filter (fun u => sig T Av u = P)

/-! ## What (4) is. -/

/-- **(4) is not a lemma toward the conclusion, it IS the conclusion.**  The `2^k`
signature classes partition `V`, so a uniform bound of `k` on every class yields
`N ≤ k·2^k` immediately.  No hypothesis about the tournament is used: not `S_k`, not
order-minimality, not `D(Av) = {v}`.  Assuming (4) is assuming `f(k) ≤ k·2^k`. -/
theorem signature_bound_gives_conclusion {T : Tournament V} {k : ℕ}
    (Av : Finset V) (hAv : Av.card = k)
    (h : ∀ P : Finset V, P ⊆ Av → (sigClass T Av P).card ≤ k) :
    Fintype.card V ≤ k * 2 ^ k := by
  have hmap : ∀ u ∈ (univ : Finset V), sig T Av u ∈ Av.powerset := by
    intro u _
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hsum := Finset.card_eq_sum_card_fiberwise hmap
  rw [Finset.card_univ] at hsum
  calc Fintype.card V
      = ∑ P ∈ Av.powerset, (univ.filter fun u => sig T Av u = P).card := hsum
    _ ≤ ∑ _P ∈ Av.powerset, k :=
        Finset.sum_le_sum (fun P hP => h P (Finset.mem_powerset.mp hP))
    _ = Av.powerset.card * k := by rw [Finset.sum_const, smul_eq_mul]
    _ = k * 2 ^ k := by rw [Finset.card_powerset, hAv]; ring

/-! ## The proof of (4). -/

/-- **The final step of Shot 19's proof of (4) is self-contradictory.**
Line 114 establishes the relation `i ⇝ j` for EVERY `i ≠ j` ("By construction this
holds for every `i ≠ j`"), and line 118 then asserts it is antisymmetric.  Those two
statements contradict each other outright, for any index type with two distinct
elements.  The contradiction at line 122 comes from the two assumptions themselves,
not from the supposed `k+1` vertices in a signature class. -/
theorem total_relation_never_antisymmetric {ι : Type*} (R : ι → ι → Prop)
    (htotal : ∀ i j : ι, i ≠ j → R i j)
    (hanti : ∀ i j : ι, R i j → ¬ R j i)
    (i j : ι) (hne : i ≠ j) : False :=
  hanti i j (htotal i j hne) (htotal j i (Ne.symm hne))

/-! ## (3) is false. -/

def P7 : Tournament (Fin 7) where
  beats a b := ((b.val + 7 - a.val) % 7) ∈ ({1, 2, 4} : Finset ℕ)
  dec := inferInstance
  irrefl := by decide
  tot := by decide

/-- **(3) is FALSE.**  Shot 19 asserts `σ_v(u) ≠ ∅` for every `u ≠ v`.  In Paley-7 the
pair `A_0 = {1,2}` is critical, its unique dominator is `0`, and the vertex `1` lies in
`A_0` with nothing in `A_0` beating it, so `σ_0(1) = ∅`. -/
theorem sigma_nonempty_false :
    Dset P7 {1, 2} = {0} ∧ (1 : Fin 7) ≠ 0 ∧ sig P7 {1, 2} 1 = ∅ := by decide

/-- The signature classes of that critical pair, at `k = 2`: sizes `2, 2, 2, 1`.
The bound `|C_P| ≤ k` is attained, and `N = 7 ≤ k·2^k = 8`. -/
theorem P7_classes :
    (sigClass P7 {1, 2} ∅).card = 2 ∧
    (sigClass P7 {1, 2} {1}).card = 2 ∧
    (sigClass P7 {1, 2} {2}).card = 2 ∧
    (sigClass P7 {1, 2} {1, 2}).card = 1 := by decide

end JSpaceShot19

#print axioms JSpaceShot19.signature_bound_gives_conclusion
#print axioms JSpaceShot19.total_relation_never_antisymmetric
#print axioms JSpaceShot19.sigma_nonempty_false
#print axioms JSpaceShot19.P7_classes
