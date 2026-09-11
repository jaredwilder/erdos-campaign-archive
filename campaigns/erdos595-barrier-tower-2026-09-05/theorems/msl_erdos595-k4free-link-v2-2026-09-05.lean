import Mathlib

set_option autoImplicit false

namespace Erdos595K4

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

theorem link_independent (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (x y z w : V) (hxy : G.Adj x y)
    (hzx : G.Adj z x) (hzy : G.Adj z y) (hwx : G.Adj w x) (hwy : G.Adj w y) :
    ¬ G.Adj z w := by
  intro hzw
  exact no_triangle_in_neighborhood G hG x y z w hxy hzx.symm hwx.symm hzy.symm hzw hwy.symm

end Erdos595K4

theorem msl_erdos595_k4free_link_v2_2026_09_05 {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4) (x y z w : V) (hxy : G.Adj x y) (hzx : G.Adj z x) (hzy : G.Adj z y) (hwx : G.Adj w x) (hwy : G.Adj w y) : ¬ G.Adj z w := by exact Erdos595K4.link_independent G hG x y z w hxy hzx hzy hwx hwy
