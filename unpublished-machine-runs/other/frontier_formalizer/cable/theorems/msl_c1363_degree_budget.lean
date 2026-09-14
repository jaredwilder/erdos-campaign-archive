set_option autoImplicit false

theorem msl_c1363_degree_budget (a b c d e f g h i j k l m : Nat) (hs : a + b + c + d + e + f + g + h + i + j + k + l + m = 20 * 6) (ha : 9 <= a) (hb : 9 <= b) (hc : 9 <= c) (hd : 9 <= d) (he : 9 <= e) (hf : 9 <= f) (hg : 9 <= g) (hh : 9 <= h) (hi : 9 <= i) (hj : 9 <= j) (hk : 9 <= k) (hl : 9 <= l) (hm : 9 <= m) : a <= 12 ∧ (a - 9) + (b - 9) + (c - 9) + (d - 9) + (e - 9) + (f - 9) + (g - 9) + (h - 9) + (i - 9) + (j - 9) + (k - 9) + (l - 9) + (m - 9) = 3 ∧ 20 * 15 - 3 * 78 = 66 ∧ 20 * 20 - 286 = 114 := by omega
