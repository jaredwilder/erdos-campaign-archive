import Mathlib

set_option autoImplicit false



/-- `ndz b m` : number of nonzero digits of `m` in base `b` (meaningful for `1 < b`),
bound semantically to core Lean's little-endian digit expansion `Nat.digits`. -/
def ndz (b : Nat) (m : Nat) : Nat := (Nat.digits b m).countP (fun d => d != 0)

/-- `binDig f m` : sum of the `f` lowest binary digits of `m`. -/
def binDig : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, m => m % 2 + binDig f (m / 2)

/-- Peeling step: one nonzero binary digit of `2 ^ (n+1)` sits at position `n+1`. -/
theorem binDig_pow_two_succ (f n : Nat) :
    binDig (f + 2) (2 ^ (n + 1)) = binDig (f + 1) (2 ^ n) := by
  have h2 : (2 ^ n * 2) % 2 = 0 := by omega
  have h3 : (2 ^ n * 2) / 2 = 2 ^ n := by omega
  calc binDig (f + 2) (2 ^ (n + 1))
      = (2 ^ (n + 1)) % 2 + binDig (f + 1) ((2 ^ (n + 1)) / 2) := rfl
    _ = (2 ^ n * 2) % 2 + binDig (f + 1) ((2 ^ n * 2) / 2) := by rw [Nat.pow_succ]
    _ = 0 + binDig (f + 1) (2 ^ n) := by rw [h2, h3]
    _ = binDig (f + 1) (2 ^ n) := rfl

/-- Clause (i) of L1, non-vacuous form: the sum of the `n+2` lowest binary digits of
`2 ^ n` is `1`; since `2 ^ n < 2 ^ (n + 2)` these are all its binary digits, so `2 ^ n`
has exactly one nonzero digit in base 2 (for every `n`). -/
theorem binDig_pow_two : ∀ n : Nat, binDig (n + 2) (2 ^ n) = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : binDig (n + 1 + 2) (2 ^ (n + 1)) = binDig (n + 1 + 1) (2 ^ n) :=
      binDig_pow_two_succ (n + 1) n
    rw [h]
    exact ih

/-- `3 ^ b` is odd. -/
theorem pow3_mod2 : ∀ b : Nat, 3 ^ b % 2 = 1 := by
  intro b
  induction b with
  | zero => rfl
  | succ c ih =>
    calc 3 ^ (c + 1) % 2
        = (3 ^ c * 3) % 2 := by rw [Nat.pow_succ]
      _ = (3 ^ c % 2 * (3 % 2)) % 2 := Nat.mul_mod _ _ _
      _ = (3 ^ c % 2 * 1) % 2 := by rw [show 3 % 2 = 1 from rfl]
      _ = (3 ^ c % 2) % 2 := by rw [Nat.mul_one]
      _ = 1 % 2 := by rw [ih]
      _ = 1 := rfl

/-- Clause (ii) hypothesis of L1, proved in file from pure core Lean:
2 and 3 are multiplicatively independent. -/
theorem mulIndep23 : ∀ (a b : Nat), 2 ^ a = 3 ^ b → a = 0 ∧ b = 0 := by
  intro a
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => exact ⟨rfl, rfl⟩
    | succ c =>
      exfalso
      rw [Nat.pow_zero, Nat.pow_succ] at h
      omega
  | succ a _ =>
    intro b h
    cases b with
    | zero =>
      exfalso
      rw [Nat.pow_zero, Nat.pow_succ] at h
      omega
    | succ c =>
      exfalso
      rw [Nat.pow_succ, Nat.pow_succ] at h
      have hR : 3 ^ (c + 1) % 2 = 1 := pow3_mod2 (c + 1)
      rw [Nat.pow_succ] at hR
      have hL : (2 ^ a * 2) % 2 = 0 := by omega
      have heq : (2 ^ a * 2) % 2 = (3 ^ c * 3) % 2 := by rw [h]
      omega

axiom PublishedTheorem_SengeStraus1971 :
  ∀ (r s k : Nat), 1 < r → 1 < s →
      (∀ (a b : Nat), r ^ a = s ^ b → a = 0 ∧ b = 0) →
      ∃ N : Nat, ∀ m : Nat, ndz r m ≤ k → ndz s m ≤ k → m < N

theorem msl_fmz_erdos406_campaign_001_R001_L1  : theorem senge_straus_instance_2_3 (k : Nat) :
    ∃ N : Nat, ∀ m : Nat, ndz 2 m ≤ k → ndz 3 m ≤ k → m < N := exact PublishedTheorem_SengeStraus1971 2 3 k (by omega) (by omega) mulIndep23

-- axiom footprint
#print axioms ndz
#print axioms binDig
#print axioms binDig_pow_two_succ
#print axioms binDig_pow_two
#print axioms pow3_mod2
#print axioms mulIndep23
#print axioms msl_fmz_erdos406_campaign_001_R001_L1
