set_option autoImplicit false

def fct : Nat → Nat
  | 0 => 1
  | (n+1) => (n+1) * fct n

def G : Nat → Nat → Nat
  | k, 0 => fct k
  | k, (m+1) => G k m * fct (k+m+1)

theorem msl_rh_benchmark_shift_telescope_006 (k m : Nat) : G (k+1) m * fct k = G k m * fct (k+m+1) := by
  induction m with
  | zero => simp [G, Nat.mul_comm]
  | succ m ih =>
    have h1 : k + 1 + m + 1 = k + m + 1 + 1 := by omega
    have h2 : k + (m + 1) + 1 = k + m + 1 + 1 := by omega
    simp only [G, h1, h2]
    rw [Nat.mul_right_comm, ih]

#print axioms msl_rh_benchmark_shift_telescope_006