import Mathlib

set_option autoImplicit false

namespace Erdos595Link

variable {V : Type*}

theorem no_triangle_in_neighborhood (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (v a b c : V) (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) : False := by
  classical
  apply hG {v, a, b, c}
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | assumption
        | exact (by assumption : G.Adj _ _).symm
  · have h1 : v ≠ a := hva.ne
    have h2 : v ≠ b := hvb.ne
    have h3 : v ≠ c := hvc.ne
    have h4 : a ≠ b := hab.ne
    have h5 : a ≠ c := hac.ne
    have h6 : b ≠ c := hbc.ne
    simp [h1, h2, h3, h4, h5, h6]

theorem link_map [DecidableEq V] (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (x y z w : V) (hxy : G.Adj x y)
    (hzx : G.Adj z x) (hzy : G.Adj z y) (hwx : G.Adj w x) (hwy : G.Adj w y)
    (hzw : z ≠ w) :
    ¬ G.Adj z w ∧ ({x, y, z} : Finset V) ≠ ({x, y, w} : Finset V) := by
  constructor
  · intro h
    exact no_triangle_in_neighborhood G hG x y z w hxy hzx.symm hwx.symm hzy.symm h hwy.symm
  · intro heq
    have hz : z ∈ ({x, y, w} : Finset V) := by
      rw [← heq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact (G.ne_of_adj hzx) rfl
    · exact (G.ne_of_adj hzy) rfl
    · exact hzw rfl

end Erdos595Link

theorem msl_erdos595_link_map_2026_09_05 {V : Type*} [DecidableEq V] (G : SimpleGraph V) (hG : G.CliqueFree 4) (x y z w : V) (hxy : G.Adj x y) (hzx : G.Adj z x) (hzy : G.Adj z y) (hwx : G.Adj w x) (hwy : G.Adj w y) (hzw : z ≠ w) : ¬ G.Adj z w ∧ ({x, y, z} : Finset V) ≠ ({x, y, w} : Finset V) := by exact Erdos595Link.link_map G hG x y z w hxy hzx hzy hwx hwy hzw
