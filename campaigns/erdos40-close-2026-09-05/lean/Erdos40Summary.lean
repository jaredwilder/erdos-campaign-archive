/-
  Erdős Problem 40 — the two pins, in one statement.

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Erdos40Ceiling
import Erdos40Turan

namespace Erdos40

open Filter Asymptotics
open scoped Topology Pointwise

/-- **The answer set of Erdős 40 is not everything**, and the exclusion is witnessed by a
genuine `g` with `g(N) → ∞` — the kind of function the problem asks about. -/
theorem exists_tendsto_atTop_not_erdos40For :
    ∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ ¬ Erdos40For g :=
  ⟨fun N : ℕ => Real.sqrt (N : ℝ) / Real.log (N : ℝ),
    tendsto_sqrt_div_log_atTop, not_erdos40For_sqrt_div_log⟩

/-- **THE TRAP.**  Any `g` in the answer set of Erdős 40 (eventually `≥ 1`) simultaneously
  * settles the Erdős–Turán conjecture (Erdős Problem 28), and
  * has threshold `√N / g(N)` strictly beyond `log N`.

So the answer set lies between an open `$500` conjecture below and an explicit
kernel-checked ceiling above. -/
theorem answer_set_trapped {g : ℕ → ℝ} (hg : ∀ᶠ N : ℕ in atTop, 1 ≤ g N)
    (H : Erdos40For g) :
    (∀ A : Set ℕ, (A + A)ᶜ.Finite → limsup (fun n : ℕ => (rep A n : ℕ∞)) atTop = ⊤) ∧
    ¬ ((fun N : ℕ => Real.sqrt (N : ℝ) / g N) =O[atTop] (fun N : ℕ => Real.log (N : ℝ))) :=
  ⟨fun A hA => erdos28_of_erdos40For hg H hA, answer_set_ceiling H⟩

end Erdos40
