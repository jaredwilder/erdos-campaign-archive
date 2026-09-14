import Mathlib

set_option autoImplicit false



namespace R008

/-- Decidable check of the full lemma content at a single s:
(1) exact valuation v₂(2^(2^s)) = 2^s, encoded as: 2^(2^s) ∣ 2^(2^s) and ¬(2^(2^s + 1) ∣ 2^(2^s));
(2) 2^s ≥ s;
(3) divisibility 2^s ∣ 2^(2^s) (witness family n = 2^s for k = 0). --/
def check_s (s : ℕ) : Bool :=
  (2 ^ (2 ^ s) ∣ 2 ^ (2 ^ s))
  && ¬ (2 ^ (2 ^ s + 1) ∣ 2 ^ (2 ^ s))
  && (s ≤ 2 ^ s)
  && ((2 ^ s : ℕ) ∣ 2 ^ (2 ^ s))

/-- Bounded check over s = 1, …, bound. --/
def check (bound : ℕ) : Bool :=
  (List.range bound).all (fun s => s = 0 || check_s s)

end R008

theorem msl_fmz_erdos479_campaign_001_R008_L1  : R008.check 6 = true := by decide

-- axiom footprint
#print axioms R008.check_s
#print axioms R008.check
#print axioms msl_fmz_erdos479_campaign_001_R008_L1
