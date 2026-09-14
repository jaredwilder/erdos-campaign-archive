import Mathlib

set_option autoImplicit false

inductive GateResult where
  | abortNoCert
  | certificate

def failClosedGate : Option Bool → Option Bool → GateResult
  | none, none => GateResult.abortNoCert
  | some _, none => GateResult.certificate
  | none, some _ => GateResult.certificate
  | some _, some _ => GateResult.certificate

theorem msl_fmz_erdos25_campaign_001_R003_L1  : ∀ (reduction residual : Option Bool), reduction = none ∧ residual = none → failClosedGate reduction residual = GateResult.abortNoCert ∧ failClosedGate reduction residual = failClosedGate reduction residual := by
  intro reduction residual h
  obtain ⟨hr, hs⟩ := h
  subst reduction
  subst residual
  exact ⟨rfl, rfl⟩
