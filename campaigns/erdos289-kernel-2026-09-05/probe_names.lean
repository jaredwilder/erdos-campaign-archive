import Mathlib
-- name probe: every #check is its own command, so unknown names report and the file continues.
#check @Nat.Prime.prime_int
#check @Int.natCast_prime
#check @Int.coe_nat_prime
#check @Finset.sum_induction
#check @Finset.sum_image
#check @Finset.sum_filter_add_sum_filter_not
#check @Nat.cast_div
#check @inv_div
#check @Rat.num_div_den
#check @Rat.den_nz
#check @Rat.den_ne_zero
#check @Rat.reduced
#check @Rat.num_ne_zero
#check @padicValRat
#check @padicValInt
#check @padicValNat.eq_zero_of_not_dvd
#check @one_le_padicValNat_of_dvd
#check @padicValNat.one_le_iff
#check @Int.natAbs_dvd_natAbs
#check @Int.natAbs_pos
#check @Int.natAbs_natCast
#check @Nat.div_pos
#check @Nat.one_le_div_iff
#check @Nat.div_mul_cancel
#check @Nat.dvd_gcd
#check @Nat.dvd_one
#check @Nat.Prime.ne_one
#check @Nat.Prime.dvd_mul
#check @Nat.Prime.pos
#check @Nat.mul_ne_zero
#check @Nat.cast_ne_zero
#check @div_add_div
#check @div_eq_iff
#check @Finset.sum_pos
#check @Finset.mem_image
#check @Finset.mem_filter
#check @Prime.dvd_mul
#check @Nat.prime_two
#check @Finset.mul_sum
#check @Finset.sum_congr
example (q : ℚ) : Nat.gcd q.num.natAbs q.den = 1 := q.reduced
example (p : ℕ) (q : ℚ) : padicValRat p q = (padicValNat p q.num.natAbs : ℤ) - (padicValNat p q.den : ℤ) := by
  unfold padicValRat padicValInt
