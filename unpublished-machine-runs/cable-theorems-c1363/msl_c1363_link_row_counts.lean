set_option autoImplicit false

theorem msl_c1363_link_row_counts (a3 a4 a5 r : Nat) (hn : a3 + a4 + a5 = 12) (hs : 3 * a3 + 4 * a4 + 5 * a5 = 5 * 9) (hr : 11 <= 4 * r) : a3 = a5 + 3 ∧ a5 <= 4 ∧ 3 <= r := by omega
