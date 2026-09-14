import Mathlib

/-!
# JSPACE SHOT 5 — adjudication in the kernel.

Shot 5 defines, for a `k`-set `A`, the **private dominators**:

  `x ∈ D(A)` is private for `A`  iff  `D(A ∪ {y}) = ∅` for every `y ∈ D(A) \ {x}` with `y → x`.

It then asserts two incompatible things about `P(A)`:

* (3)  `|P(A)| ≥ k/4` for at least half of all `k`-sets;
* (16) no `k`-set has two private dominators, i.e. `|P(A)| ≤ 1`.

The truth is proved here, and it refutes both at once:

  **`|P(A)| ≤ 2` for every tournament, every `A`, every `k`.**  (`private_card_le_two`)

`|P(A)|` is bounded by an absolute constant, so (3) fails for every `k ≥ 9`,
and with it (4), (11), (12), (15).  (16) is off by one: `|P(A)| = 2` really occurs.

The mechanism: `D(A ∪ {y}) = ∅` says exactly that `y` is a SOURCE of `T[D(A)]`
(`empty_iff_source`), and a tournament has at most one source (`source_unique`).
-/

namespace JSpaceShot5

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

theorem mem_Dset {T : Tournament V} {A : Finset V} {v : V} :
    v ∈ Dset T A ↔ ∀ a ∈ A, T.beats v a := by
  simp [Dset]

/-- In a tournament, `a ≠ b` and `¬ beats b a` give `beats a b`. -/
theorem beats_of_not {T : Tournament V} {a b : V} (hne : a ≠ b) (h : ¬ T.beats b a) :
    T.beats a b := by
  by_contra hc
  exact h ((T.tot b a (Ne.symm hne)).mpr hc)

/-- `s` is a source of `S`: it beats every other member. -/
def IsSource (T : Tournament V) (S : Finset V) (s : V) : Prop :=
  s ∈ S ∧ ∀ y ∈ S, y ≠ s → T.beats s y

/-- Shot 5's privacy predicate, verbatim. -/
def IsPrivate (T : Tournament V) (A : Finset V) (x : V) : Prop :=
  ∀ y ∈ Dset T A, y ≠ x → T.beats y x → Dset T (insert y A) = ∅

instance decIsPrivate (T : Tournament V) (A : Finset V) :
    DecidablePred (IsPrivate T A) := by
  intro x
  unfold IsPrivate
  infer_instance

/-- `D(A ∪ {y}) = ∅` says exactly that `y` is a source of `D(A)`. -/
theorem empty_iff_source {T : Tournament V} {A : Finset V} {y : V} (hy : y ∈ Dset T A) :
    Dset T (insert y A) = ∅ ↔ IsSource T (Dset T A) y := by
  constructor
  · intro h
    refine ⟨hy, fun z hz hzy => ?_⟩
    by_contra hc
    have hzy' : T.beats z y := beats_of_not hzy hc
    have hmem : z ∈ Dset T (insert y A) := by
      refine mem_Dset.mpr (fun a ha => ?_)
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · exact hzy'
      · exact mem_Dset.mp hz a ha'
    rw [h] at hmem
    simp at hmem
  · rintro ⟨-, hsrc⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    have hzy : T.beats z y := mem_Dset.mp hz y (Finset.mem_insert_self _ _)
    have hzD : z ∈ Dset T A :=
      mem_Dset.mpr (fun a ha => mem_Dset.mp hz a (Finset.mem_insert_of_mem ha))
    by_cases hzeq : z = y
    · subst hzeq
      exact T.irrefl z hzy
    · exact ((T.tot y z (Ne.symm hzeq)).mp (hsrc z hzD hzeq)) hzy

/-- A tournament has at most one source. -/
theorem source_unique {T : Tournament V} {S : Finset V} {s t : V}
    (hs : IsSource T S s) (ht : IsSource T S t) : s = t := by
  by_contra hne
  have h1 : T.beats s t := hs.2 t ht.1 (Ne.symm hne)
  have h2 : T.beats t s := ht.2 s hs.1 hne
  exact ((T.tot s t hne).mp h1) h2

/-- **THE KILL.** `|P(A)| ≤ 2` for every tournament and every `A`. -/
theorem private_card_le_two (T : Tournament V) (A : Finset V) :
    ((Dset T A).filter (IsPrivate T A)).card ≤ 2 := by
  by_contra hc
  push_neg at hc
  obtain ⟨a, b, c, ha, hb, hcc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hc
  obtain ⟨haD, haP⟩ := mem_filter.mp ha
  obtain ⟨hbD, hbP⟩ := mem_filter.mp hb
  obtain ⟨hcD, hcP⟩ := mem_filter.mp hcc
  -- any in-neighbour (inside D) of a private vertex is a source of D
  have key : ∀ x y : V, y ∈ Dset T A → IsPrivate T A x → y ≠ x → T.beats y x →
      IsSource T (Dset T A) y := by
    intro x y hyD hxP hyx hbeat
    exact (empty_iff_source hyD).mp (hxP y hyD hyx hbeat)
  rcases (em (T.beats a b)) with hab1 | hab1
  · -- a → b, so a is a source of D
    have hsa : IsSource T (Dset T A) a := key b a haD hbP hab hab1
    rcases (em (T.beats b c)) with hbc1 | hbc1
    · have hsb : IsSource T (Dset T A) b := key c b hbD hcP hbc hbc1
      exact hab (source_unique hsa hsb)
    · have hcb : T.beats c b := beats_of_not (Ne.symm hbc) hbc1
      have hsc : IsSource T (Dset T A) c := key b c hcD hbP (Ne.symm hbc) hcb
      exact hac (source_unique hsa hsc)
  · -- b → a, so b is a source of D
    have hba : T.beats b a := beats_of_not (Ne.symm hab) hab1
    have hsb : IsSource T (Dset T A) b := key a b hbD haP (Ne.symm hab) hba
    rcases (em (T.beats a c)) with hac1 | hac1
    · have hsa : IsSource T (Dset T A) a := key c a haD hcP hac hac1
      exact hab (source_unique hsa hsb)
    · have hca : T.beats c a := beats_of_not (Ne.symm hac) hac1
      have hsc : IsSource T (Dset T A) c := key a c hcD haP (Ne.symm hac) hca
      exact hbc (source_unique hsb hsc)

/-- **(3) is FALSE for every `k ≥ 9`.** It demands `k/4` private dominators;
there are never more than two. -/
theorem eq3_false (T : Tournament V) (A : Finset V) (k : ℕ) (hk : 9 ≤ k) :
    4 * ((Dset T A).filter (IsPrivate T A)).card < k := by
  have := private_card_le_two T A
  omega

end JSpaceShot5

#print axioms JSpaceShot5.empty_iff_source
#print axioms JSpaceShot5.source_unique
#print axioms JSpaceShot5.private_card_le_two
#print axioms JSpaceShot5.eq3_false
