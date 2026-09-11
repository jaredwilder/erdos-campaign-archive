/-
Erdős #500 — name/shape reconnaissance against the pinned Mathlib (919544d4).
Nothing here is a result. It exists so `Attack01.lean` does not guess a lemma name.
-/
import Mathlib

-- === double counting ===
#check @Finset.card_mul_le_card_mul
#check @Finset.bipartiteAbove
#check @Finset.bipartiteBelow

-- === cardinality plumbing ===
#check @Finset.card_le_card_of_injOn
#check @Finset.card_compl
#check @Finset.card_insert_of_notMem
#check @Finset.exists_subset_card_eq
#check @Finset.ssubset_iff_of_subset
#check @Finset.card_lt_card
#check @Finset.card_powersetCard
#check @Finset.card_union_of_disjoint
#check @Finset.card_erase_of_mem
#check @Finset.eq_univ_of_card
#check @Finset.notMem_erase
#check @Finset.mem_of_mem_erase
#check @Finset.filter_true_of_mem
#check @Finset.filter_eq_empty_iff
#check @Finset.filter_union
#check @Finset.card_eq_sum_card_fiberwise
#check @Finset.disjoint_left
#check @Finset.mem_compl
#check @Finset.mem_coe
#check @Fin.sum_univ_three

-- === sSup on ℕ ===
#check @Nat.sSup_mem
#check @Nat.choose_succ_right_eq
#check @Nat.choose_pos
#check @Nat.le_of_mul_le_mul_right

-- === real / filter plumbing ===
#check @div_le_iff₀
#check @le_div_iff₀
#check @le_of_tendsto
#check @ge_of_tendsto
#check @le_of_forall_pos_le_add
#check @Filter.eventually_ge_atTop

-- === Fin 3 arithmetic facts the attack needs ===
example : ∀ j j' : Fin 3, j' = j ∨ j' = j + 1 ∨ j' = j + 2 := by decide
example : ∀ j : Fin 3, j + 2 ≠ j := by decide
example : ∀ j : Fin 3, j + 1 ≠ j := by decide
example : ∀ j : Fin 3, j + 1 ≠ j + 2 := by decide

-- === kernel-evaluation feasibility for the Turán construction ===
namespace Probe500

def partOf {n : ℕ} (v : Fin n) : Fin 3 :=
  ⟨(v : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩

def partCard {n : ℕ} (e : Finset (Fin n)) (j : Fin 3) : ℕ :=
  (e.filter (fun v => partOf v = j)).card

def TuranAdmissible {n : ℕ} (e : Finset (Fin n)) : Prop :=
  (∀ j : Fin 3, partCard e j = 1) ∨ (∃ j : Fin 3, partCard e j = 2 ∧ partCard e (j + 1) = 1)

instance decTuranAdmissible {n : ℕ} (e : Finset (Fin n)) : Decidable (TuranAdmissible e) := by
  unfold TuranAdmissible
  infer_instance

def turanEdges (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.powersetCard 3 (Finset.univ : Finset (Fin n))).filter TuranAdmissible

-- expected: 3 (parts {0,3},{1},{2}: 2·1·1 transversal + C(2,2)·1 = 2 + 1)
example : (turanEdges 4).card = 3 := by decide
-- expected: 7 (parts {0,3},{1,4},{2}: 2·2·1 + C(2,2)·2 + C(2,2)·1 = 4 + 2 + 1)
example : (turanEdges 5).card = 7 := by decide
-- expected: 14 (parts of size 2,2,2: 8 transversal + 3·C(2,2)·2 = 8 + 6)
example : (turanEdges 6).card = 14 := by decide

end Probe500
