/-
Erdős Problem 564  --  https://www.erdosproblems.com/564   ($500, OPEN)

  Let R_3(n) be the least m such that every 2-colouring of the triples of an m-set
  contains a monochromatic n-set.  Is there c > 0 with  R_3(n) ≥ 2^(2^(c n)) ?

This file is a *partial* development: it does NOT decide 564.  It builds the
reusable kernel-checked scaffolding around `hypergraphRamsey` that the
formal-conjectures corpus lacks, and proves the reduction that any attack uses.

Everything below is sorry-free.

Contents
  * `RamseySet r n`                 : the set of admissible host sizes
  * `ramseySet_upward`              : admissibility is upward closed  (injection transfer)
  * `lt_hypergraphRamsey_iff`       : m < R_r(n)  ↔  m admits a witness colouring
  * `ramseySet_shrink`              : R_r(n) ≤ R_{r+1}(n+1)          (max-deletion cone)
  * `erdos564_of_colourings`        : 564 follows from a family of witness colourings
-/
import Mathlib

namespace Erdos564

open Finset Filter

/-- `RamseySet r n` is the set of host sizes `m` for which *every* 2-colouring of the
`r`-subsets of a set of size `m` contains a monochromatic subset of size `n`.

This is the set whose infimum defines the hypergraph Ramsey number; the definition is
taken verbatim from `FormalConjecturesForMathlib.Combinatorics.Ramsey` so that the
results here transfer to `Combinatorics.hypergraphRamsey`. -/
def RamseySet (r n : ℕ) : Set ℕ :=
  { m | ∀ c : Finset (Fin m) → Bool,
      ∃ S : Finset (Fin m), S.card = n ∧
        ∃ b : Bool, ∀ e : Finset (Fin m), e ⊆ S → e.card = r → c e = b }

/-- The `r`-uniform 2-colour hypergraph Ramsey number `R_r(n)`. -/
noncomputable def hypergraphRamsey (r n : ℕ) : ℕ := sInf (RamseySet r n)

/-! ### Transfer along an injection -/

/-- The canonical embedding `Fin m ↪ Fin m'` when `m ≤ m'`. -/
def finEmb {m m' : ℕ} (h : m ≤ m') : Fin m ↪ Fin m' where
  toFun i := ⟨i.1, lt_of_lt_of_le i.2 h⟩
  inj' := by
    intro a b hab
    apply Fin.val_injective
    have h1 := congrArg (fun x : Fin m' => (x : ℕ)) hab
    simpa using h1

/-- Admissibility is upward closed: a larger host is only harder to colour. -/
theorem ramseySet_upward {r n m m' : ℕ} (h : m ≤ m') (hm : m ∈ RamseySet r n) :
    m' ∈ RamseySet r n := by
  intro c
  obtain ⟨S, hScard, b, hb⟩ := hm (fun A => c (A.map (finEmb h)))
  refine ⟨S.map (finEmb h), by simpa using hScard, b, ?_⟩
  intro e he hecard
  obtain ⟨A, hA, rfl⟩ := Finset.subset_map_iff.mp he
  have hAcard : A.card = r := by simpa using hecard
  exact hb A hA hAcard

/-! ### The threshold characterisation

`hypergraphRamsey` is an `sInf`, which is only usable once one knows the underlying
set is an up-set.  With `ramseySet_upward` in hand it becomes a genuine threshold:
`m < R_r(n)` says exactly that `m` carries a witness colouring. -/

theorem not_mem_ramseySet_of_lt {r n m : ℕ} (h : m < hypergraphRamsey r n) :
    m ∉ RamseySet r n := fun hm => absurd (Nat.sInf_le hm) (not_le.mpr h)

theorem lt_hypergraphRamsey_of_not_mem {r n m : ℕ} (hne : (RamseySet r n).Nonempty)
    (h : m ∉ RamseySet r n) : m < hypergraphRamsey r n := by
  rcases Nat.lt_or_ge m (hypergraphRamsey r n) with h' | h'
  · exact h'
  · exact absurd (ramseySet_upward h' (Nat.sInf_mem hne)) h

/-- **Threshold characterisation.**  Below the Ramsey number, and only there, a witness
colouring exists. -/
theorem lt_hypergraphRamsey_iff {r n m : ℕ} (hne : (RamseySet r n).Nonempty) :
    m < hypergraphRamsey r n ↔ m ∉ RamseySet r n :=
  ⟨not_mem_ramseySet_of_lt, lt_hypergraphRamsey_of_not_mem hne⟩

/-- To show a host size `N` is *not* admissible it suffices to exhibit a colouring with no
monochromatic `n`-set on *any* type into which `Fin N` embeds. -/
theorem not_mem_ramseySet_of_colouring {N r n : ℕ} {α : Type*} [DecidableEq α]
    (f : Fin N ↪ α) (C : Finset α → Bool)
    (hC : ∀ S : Finset α, S.card = n → ∀ b : Bool, ∃ e ⊆ S, e.card = r ∧ C e ≠ b) :
    N ∉ RamseySet r n := by
  intro hmem
  obtain ⟨S, hScard, b, hb⟩ := hmem (fun A => C (A.map f))
  obtain ⟨e, he, hecard, hbad⟩ := hC (S.map f) (by simpa using hScard) b
  obtain ⟨A, hA, rfl⟩ := Finset.subset_map_iff.mp he
  exact hbad (hb A hA (by simpa using hecard))

/-! ### The max-deletion cone: `R_r(n) ≤ R_{r+1}(n+1)` -/

/-- Delete the largest element of a finset (identity on `∅`). -/
noncomputable def dropMax {m : ℕ} (A : Finset (Fin m)) : Finset (Fin m) :=
  if h : A.Nonempty then A.erase (A.max' h) else A

theorem dropMax_insert {m : ℕ} {M : Fin m} {A : Finset (Fin m)}
    (hM : M ∉ A) (hle : ∀ a ∈ A, a ≤ M) : dropMax (insert M A) = A := by
  have hne : (insert M A).Nonempty := ⟨M, Finset.mem_insert_self _ _⟩
  have hmax : (insert M A).max' hne = M := by
    refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (Finset.mem_insert_self _ _))
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact le_rfl
    · exact hle y hy
  rw [dropMax, dif_pos hne, hmax, Finset.erase_insert hM]

/-- **Cone / max-deletion lemma.**  If every 2-colouring of the `(r+1)`-subsets of `[m]`
has a monochromatic `(n+1)`-set, then every 2-colouring of the `r`-subsets of `[m]` has a
monochromatic `n`-set.

Given a colouring `c` of `r`-sets, colour an `(r+1)`-set by `c` applied to it with its
largest element removed; a monochromatic `(n+1)`-set `S` then yields the monochromatic
`n`-set `S \ {max S}`. -/
theorem ramseySet_shrink {r n m : ℕ} (hm : m ∈ RamseySet (r + 1) (n + 1)) :
    m ∈ RamseySet r n := by
  intro c
  obtain ⟨S, hScard, b, hb⟩ := hm (fun A => c (dropMax A))
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  set M := S.max' hSne with hMdef
  have hMS : M ∈ S := Finset.max'_mem _ _
  refine ⟨S.erase M, ?_, b, ?_⟩
  · rw [Finset.card_erase_of_mem hMS, hScard]
    omega
  · intro e he hecard
    have hMe : M ∉ e := fun hc => (Finset.mem_erase.mp (he hc)).1 rfl
    have hle : ∀ a ∈ e, a ≤ M := fun a ha =>
      Finset.le_max' _ _ (Finset.mem_of_mem_erase (he ha))
    have hsub : insert M e ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hMS
      · exact Finset.mem_of_mem_erase (he hx)
    have hcard : (insert M e).card = r + 1 := by
      rw [Finset.card_insert_of_notMem hMe, hecard]
    have hval := hb (insert M e) hsub hcard
    simpa [dropMax_insert hMe hle] using hval

/-- `R_r(n) ≤ R_{r+1}(n+1)`.  In particular `R_2(n) ≤ R_3(n+1)`: the quantity in
Erdős 564 dominates the graph Ramsey number. -/
theorem hypergraphRamsey_shrink {r n : ℕ} (hne : (RamseySet (r + 1) (n + 1)).Nonempty) :
    hypergraphRamsey r n ≤ hypergraphRamsey (r + 1) (n + 1) :=
  Nat.sInf_le (ramseySet_shrink (Nat.sInf_mem hne))

theorem graphRamsey_le_hypergraphRamsey {n : ℕ} (hne : (RamseySet 3 (n + 1)).Nonempty) :
    hypergraphRamsey 2 n ≤ hypergraphRamsey 3 (n + 1) :=
  hypergraphRamsey_shrink hne

/-! ### Erdős 564 -/

/-- The assertion of Erdős problem 564 (statement as formalised in
`FormalConjectures.ErdosProblems.564`). -/
def Erdos564Claim : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (2 : ℝ) ^ (c * (n : ℝ)) ≤ hypergraphRamsey 3 n

/-- **The reduction an attack on 564 actually uses.**  To prove 564 it suffices to
exhibit, for all large `n`, a single 2-colouring of the triples of a host of size at
least `2^(2^(cn))` with no monochromatic `n`-set.

This converts the `sInf`-shaped analytic statement into a purely combinatorial
construction problem, which is the form in which every known lower bound
(Erdős–Hajnal stepping-up, and its multicolour refinements) is proved. -/
theorem erdos564_of_colourings
    (hne : ∀ n, (RamseySet 3 n).Nonempty)
    (c : ℝ) (hc : 0 < c)
    (H : ∀ᶠ n : ℕ in atTop,
      ∃ N : ℕ, (2 : ℝ) ^ (2 : ℝ) ^ (c * (n : ℝ)) ≤ (N : ℝ) ∧ N ∉ RamseySet 3 n) :
    Erdos564Claim := by
  refine ⟨c, hc, ?_⟩
  filter_upwards [H] with n hn
  obtain ⟨N, hN, hNnot⟩ := hn
  have hlt : N < hypergraphRamsey 3 n := lt_hypergraphRamsey_of_not_mem (hne n) hNnot
  refine hN.trans ?_
  exact_mod_cast hlt.le

/-! ## An unconditional explicit lower bound: `R_3(n) > 2^(n-3)`

The host is the family of subsets of `Fin m`, ordered colexicographically, so that the
"largest coordinate at which two hosts differ" — the `δ` of the Erdős–Hajnal stepping-up
apparatus — is available as `Finset.max` of a symmetric difference, and the colex order is
*defined* by which side that coordinate lies on.

A triple `u < v < w` is coloured by whether `δ(u,v) < δ(v,w)`.  Along a monochromatic set,
consecutive `δ`'s are then strictly monotone (the two `δ`'s of a triple can never be equal,
which is the one genuine lemma here), so a monochromatic set has at most `m + 2` elements.
-/

section Construction

open scoped symmDiff
open Finset.Colex

/-- The host: subsets of `Fin m`, linearly ordered colexicographically. -/
abbrev Host (m : ℕ) := Colex (Finset (Fin m))

instance instFintypeHost (m : ℕ) : Fintype (Host m) :=
  inferInstanceAs (Fintype (Finset (Fin m)))

instance instDecEqHost (m : ℕ) : DecidableEq (Host m) :=
  inferInstanceAs (DecidableEq (Finset (Fin m)))

theorem card_host (m : ℕ) : Fintype.card (Host m) = 2 ^ m := by
  show Fintype.card (Finset (Fin m)) = 2 ^ m
  simp

/-- `delta u v` is the largest coordinate at which the hosts `u` and `v` differ,
and `⊥` exactly when `u = v`.  This is the `δ` of the stepping-up apparatus. -/
noncomputable def delta {m : ℕ} (u v : Host m) : WithBot (Fin m) :=
  (ofColex u ∆ ofColex v).max

/-- The defining property of colex: the top differing coordinate of `u < v` belongs to `v`
and not to `u`. -/
theorem delta_spec {m : ℕ} {u v : Host m} (h : u < v) :
    ∃ a : Fin m, delta u v = (a : WithBot (Fin m)) ∧ a ∈ ofColex v ∧ a ∉ ofColex u := by
  obtain ⟨hne, hmem⟩ := lt_iff_max'_mem.mp h
  refine ⟨_, ?_, hmem, ?_⟩
  · rw [delta, ← Finset.coe_max']
  · have hsd := Finset.max'_mem (ofColex u ∆ ofColex v) (Finset.symmDiff_nonempty.2 hne)
    rw [Finset.mem_symmDiff] at hsd
    rcases hsd with ⟨_, hnv⟩ | ⟨_, hnu⟩
    · exact absurd hmem hnv
    · exact hnu

/-- **The one genuine lemma.**  For `u < v < w` the two `δ`'s of the triple differ: the first
lies in `v`, the second does not. -/
theorem delta_ne {m : ℕ} {u v w : Host m} (huv : u < v) (hvw : v < w) :
    delta u v ≠ delta v w := by
  obtain ⟨a, ha, hav, -⟩ := delta_spec huv
  obtain ⟨c, hc, -, hcv⟩ := delta_spec hvw
  rw [ha, hc]
  intro hcon
  exact hcv (by rwa [WithBot.coe_eq_coe.mp hcon] at hav)

/-- The colouring: a triple `u < v < w` is `true` exactly when `δ(u,v) < δ(v,w)`. -/
noncomputable def col {m : ℕ} (e : Finset (Host m)) : Bool :=
  if h : e.card = 3 then
    decide (delta (e.orderEmbOfFin h 0) (e.orderEmbOfFin h 1) <
            delta (e.orderEmbOfFin h 1) (e.orderEmbOfFin h 2))
  else false

theorem col_triple {m : ℕ} {a b c : Host m} (hab : a < b) (hbc : b < c) :
    col ({a, b, c} : Finset (Host m)) = decide (delta a b < delta b c) := by
  have hac : a < c := hab.trans hbc
  have hcard : ({a, b, c} : Finset (Host m)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab.ne, hac.ne]),
      Finset.card_insert_of_notMem (by simp [hbc.ne]), Finset.card_singleton]
  have hmono : StrictMono (![a, b, c] : Fin 3 → Host m) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def] <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
      first
        | exact hab
        | exact hbc
        | exact hac
  have hmem : ∀ x : Fin 3, (![a, b, c] : Fin 3 → Host m) x ∈ ({a, b, c} : Finset (Host m)) := by
    intro x; fin_cases x <;> simp
  have key := Finset.orderEmbOfFin_unique hcard hmem hmono
  rw [col, dif_pos hcard, ← key]
  simp

/-- A monochromatic set has at most `m + 2` elements. -/
theorem mono_card_le {m : ℕ} {S : Finset (Host m)} {b : Bool}
    (hb : ∀ e ⊆ S, e.card = 3 → col e = b) : S.card ≤ m + 2 := by
  set k := S.card with hk
  by_contra hcon
  push_neg at hcon
  have hk3 : 3 ≤ k := by omega
  set g := S.orderEmbOfFin hk.symm with hg
  -- the sequence of consecutive `δ`'s
  set d : ℕ → WithBot (Fin m) := fun j =>
    if h : j + 1 < k then delta (g ⟨j, by omega⟩) (g ⟨j + 1, h⟩) else ⊥ with hd
  have adj : ∀ p, p + 2 < k →
      (if b then d p < d (p + 1) else d (p + 1) < d p) := by
    intro p hp
    have h0 : p < k := by omega
    have h1 : p + 1 < k := by omega
    have h2 : p + 2 < k := hp
    set u := g ⟨p, h0⟩ with hu
    set v := g ⟨p + 1, h1⟩ with hv
    set w := g ⟨p + 2, h2⟩ with hw
    have huv : u < v := g.strictMono (by simp [Fin.lt_def])
    have hvw : v < w := g.strictMono (by simp [Fin.lt_def])
    have hsub : ({u, v, w} : Finset (Host m)) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;>
        exact Finset.orderEmbOfFin_mem _ _ _
    have hcard : ({u, v, w} : Finset (Host m)).card = 3 := by
      have hac : u < w := huv.trans hvw
      rw [Finset.card_insert_of_notMem (by simp [huv.ne, hac.ne]),
        Finset.card_insert_of_notMem (by simp [hvw.ne]), Finset.card_singleton]
    have hcol := hb _ hsub hcard
    rw [col_triple huv hvw] at hcol
    have hdp : d p = delta u v := by rw [hd]; simp only [dif_pos h1]; rfl
    have hdp1 : d (p + 1) = delta v w := by
      rw [hd]; simp only [dif_pos h2]; rfl
    have hne := delta_ne huv hvw
    cases b with
    | true =>
      simp only [if_true, hdp, hdp1]
      simpa using hcol
    | false =>
      simp only [if_false, hdp, hdp1]
      have : ¬ (delta u v < delta v w) := by simpa using hcol
      exact lt_of_le_of_ne (not_lt.mp this) hne.symm
  -- consecutive strictness propagates to a strict order along the whole sequence
  have chain : ∀ j, j < k - 1 → ∀ i, i < j → (if b then d i < d j else d j < d i) := by
    intro j
    induction j with
    | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ p ih =>
      intro hp i hi
      have hstep := adj p (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · have hprev := ih (by omega) i h
        cases b with
        | true => exact lt_trans (by simpa using hprev) (by simpa using hstep)
        | false => exact lt_trans (by simpa using hstep) (by simpa using hprev)
      · subst h; exact hstep
  have hinj : ∀ i ∈ Finset.range (k - 1), ∀ j ∈ Finset.range (k - 1), d i = d j → i = j := by
    intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    by_contra hne
    rcases Nat.lt_or_ge i j with h | h
    · have hch := chain j hj i h
      cases b with
      | true =>
        have h' : d i < d j := by simpa using hch
        exact absurd hij h'.ne
      | false =>
        have h' : d j < d i := by simpa using hch
        exact absurd hij.symm h'.ne
    · have hji : j < i := lt_of_le_of_ne h (Ne.symm hne)
      have hch := chain i hi j hji
      cases b with
      | true =>
        have h' : d j < d i := by simpa using hch
        exact absurd hij.symm h'.ne
      | false =>
        have h' : d i < d j := by simpa using hch
        exact absurd hij h'.ne
  have hle : (Finset.range (k - 1)).card ≤ (Finset.univ : Finset (WithBot (Fin m))).card :=
    Finset.card_le_card_of_injOn d (fun a _ => Finset.mem_univ _) hinj
  have hcardWB : (Finset.univ : Finset (WithBot (Fin m))).card = m + 1 := by
    rw [Finset.card_univ]
    show Fintype.card (Option (Fin m)) = m + 1
    simp
  rw [Finset.card_range, hcardWB] at hle
  omega

/-- **Unconditional explicit lower bound.**  A host of size `2^m` carries a 2-colouring of its
triples with no monochromatic set of size `m + 3`; equivalently `R_3(m+3) > 2^m`. -/
theorem not_mem_ramseySet_pow (m : ℕ) : 2 ^ m ∉ RamseySet 3 (m + 3) := by
  refine not_mem_ramseySet_of_colouring
    (Fintype.equivFinOfCardEq (card_host m)).symm.toEmbedding col ?_
  intro S hScard b
  by_contra hcon
  push_neg at hcon
  have hmono : ∀ e ⊆ S, e.card = 3 → col e = b := by
    intro e he hecard
    by_contra hne
    exact hne (by simpa using hcon e he hecard)
  have := mono_card_le hmono
  omega

/-- `R_3(n) > 2^(n-3)`, given that the Ramsey number is well defined at all. -/
theorem pow_lt_hypergraphRamsey (m : ℕ) (hne : (RamseySet 3 (m + 3)).Nonempty) :
    2 ^ m < hypergraphRamsey 3 (m + 3) :=
  lt_hypergraphRamsey_of_not_mem hne (not_mem_ramseySet_pow m)

end Construction

end Erdos564
