/-
  JSPACE SHOT 1 -- Lean fire point (★).

  Claim (★):  for any tournament U,
      Σ_{x∈U} d⁻(x)(d⁻(x)-1)  ≤  |U|(|U|-1)(|U|-3)/4.

  Stated over ℤ with the /4 cleared:
      4 * Σ d⁻(x)(d⁻(x)-1)  ≤  n(n-1)(n-3).

  REFUTED.  Witness: the transitive tournament on 4 vertices (a beats b iff a<b).
  Zero-dependency: Lean 4 core only, no Mathlib, closed by `decide` (kernel evaluation).
-/

abbrev V := Fin 4

def verts : List V := [0, 1, 2, 3]

/-- `beats a b` : a → b.  Transitive tournament: a beats b iff a < b. -/
def beats (a b : V) : Bool := a.val < b.val

/-- in-degree: how many vertices beat x -/
def dminus (x : V) : Int := (verts.filter (fun y => beats y x)).length

def lhs : Int := (verts.map (fun x => dminus x * (dminus x - 1))).sum

def n : Int := verts.length

def rhs : Int := n * (n - 1) * (n - 3)

-- sanity: it really is a tournament (exactly one orientation per unordered pair)
theorem is_tournament :
    ∀ a ∈ verts, ∀ b ∈ verts, a ≠ b → (beats a b = true) ≠ (beats b a = true) := by
  decide

-- the two sides, evaluated by the kernel
theorem lhs_val : lhs = 8 := by decide
theorem rhs_val : rhs = 12 := by decide

/-- ★ FAILS on this witness: 4·8 = 32 > 12. -/
theorem star_refuted : ¬ (4 * lhs ≤ rhs) := by decide

/-- Restated in the shot's own form: LHS exceeds n(n-1)(n-3)/4 = 3. -/
theorem star_refuted_quarter : rhs / 4 = 3 ∧ lhs = 8 ∧ ¬ (lhs * 4 ≤ rhs) := by decide

/-- The true sharp bound at the same witness: Σ d⁻(d⁻-1) = 2·C(n,3) = n(n-1)(n-2)/3. -/
theorem true_value_is_transitive_max : 3 * lhs = n * (n - 1) * (n - 2) := by decide
