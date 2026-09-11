import Mathlib

set_option autoImplicit false

namespace Erdos595Lin

variable {V : Type*}

theorem triple_of_card_three [DecidableEq V] (T : Finset V) (hT : T.card = 3)
    (x y z : V) (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : T = {x, y, z} := by
  have hsub : ({x, y, z} : Finset V) ⊆ T := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have hcard : ({x, y, z} : Finset V).card = 3 := by
    simp [hxy, hyz, hxz]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hT, hcard])).symm

theorem two_triangles_share_at_most_one_edge [DecidableEq V] (G : SimpleGraph V)
    (T1 T2 : Finset V) (h1 : G.IsNClique 3 T1) (h2 : G.IsNClique 3 T2)
    (x y z : V) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hx1 : x ∈ T1) (hy1 : y ∈ T1) (hz1 : z ∈ T1)
    (hx2 : x ∈ T2) (hy2 : y ∈ T2) (hz2 : z ∈ T2) : T1 = T2 := by
  rw [triple_of_card_three T1 h1.2 x y z hx1 hy1 hz1 hxy hyz hxz,
      triple_of_card_three T2 h2.2 x y z hx2 hy2 hz2 hxy hyz hxz]

end Erdos595Lin

theorem msl_erdos595_hypergraph_linear_2026_09_05 {V : Type*} [DecidableEq V] (G : SimpleGraph V) (T1 T2 : Finset V) (h1 : G.IsNClique 3 T1) (h2 : G.IsNClique 3 T2) (x y z : V) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (hx1 : x ∈ T1) (hy1 : y ∈ T1) (hz1 : z ∈ T1) (hx2 : x ∈ T2) (hy2 : y ∈ T2) (hz2 : z ∈ T2) : T1 = T2 := by exact Erdos595Lin.two_triangles_share_at_most_one_edge G T1 T2 h1 h2 x y z hxy hyz hxz hx1 hy1 hz1 hx2 hy2 hz2
