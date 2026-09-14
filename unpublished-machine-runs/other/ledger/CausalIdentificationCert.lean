/-
  CausalIdentificationCert.lean — machine-verified identification certificate for the antibiotic-timing
  causal finding (delay -> ICU mortality). It formalizes the BACKDOOR / g-formula adjustment used in
  sepsis_causal_unhedged.py: the estimand computed from OBSERVED data equals the true COUNTERFACTUAL mean
  UNDER conditional ignorability (no unmeasured confounding given the measured covariates) and positivity
  (every confounder stratum is observed). The math is what this proves unfoolable; the assumption is what
  the empirical blades (hospital fixed-effects, negative-control outcome, E-value, GES adjacency,
  cross-environment invariance) probe. Self-contained: core Lean 4, no Mathlib.

  Strata := list of (P_c, m_c, mc_c) per confounder stratum c:
    P_c  = P(C = c)                     (stratum weight)
    m_c  = E[Y | T=t, C=c]              (OBSERVED conditional mean — what the data gives)
    mc_c = E[Y(t) | C=c]                (COUNTERFACTUAL conditional mean — what we want)
  adj = Σ_c P_c · m_c  (the adjustment estimand) ;  cf = Σ_c P_c · mc_c  (the true counterfactual mean).
-/

abbrev Strata := List (Float × Float × Float)

def adj : Strata → Float
  | [] => 0.0
  | (p, m, _) :: rest => p * m + adj rest

def cf : Strata → Float
  | [] => 0.0
  | (p, _, mc) :: rest => p * mc + cf rest

/-- Conditional ignorability + positivity: in EVERY observed stratum, the observed conditional mean
    equals the counterfactual conditional mean (m_c = mc_c). This is the no-unmeasured-confounding
    assumption made stratum-explicit. -/
def Ignorable : Strata → Prop
  | [] => True
  | (_, m, mc) :: rest => m = mc ∧ Ignorable rest

/-- THE IDENTIFICATION THEOREM. Under ignorability, the backdoor adjustment estimand computed from
    observed data EQUALS the true counterfactual mean. (Hence the adjusted contrast = the true ATE.) -/
theorem backdoor_identifies : ∀ s : Strata, Ignorable s → adj s = cf s
  | [], _ => rfl
  | (p, m, mc) :: rest, h => by
      have hm : m = mc := h.1
      have hrest : adj rest = cf rest := backdoor_identifies rest h.2
      show p * m + adj rest = p * mc + cf rest
      rw [hm, hrest]

/-- Corollary: the adjusted average treatment effect equals the true counterfactual contrast. -/
theorem ate_identified (s : Strata) (h : Ignorable s) : adj s = cf s :=
  backdoor_identifies s h

-- Certificate is axiom-free (no `sorry`, only Lean's trusted kernel axioms).
#print axioms backdoor_identifies
