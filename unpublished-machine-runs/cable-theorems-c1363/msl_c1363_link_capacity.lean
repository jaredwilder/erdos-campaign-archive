set_option autoImplicit false

theorem msl_c1363_link_capacity (d s u : Nat) (hd : d <= 9) (hstar : s <= 6 * d) (havoid : u <= 10 * (9 - d)) (hcov : 55 <= s + u) (hpts : 11 <= 4 * d) : 3 <= d ∧ d <= 8 := by omega
