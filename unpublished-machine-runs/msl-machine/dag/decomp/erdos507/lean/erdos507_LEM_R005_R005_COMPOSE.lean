import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

inductive InputKind where
  | missing : InputKind
  | perContract : InputKind
  | concrete : InputKind
deriving DecidableEq

inductive Claim where
  | proof : Claim
  | computation : Claim
deriving DecidableEq

inductive Verdict where
  | aborted : Verdict
  | certified : Claim → Verdict
deriving DecidableEq

structure CertifierInput where
  kind : InputKind
  claim : Claim
  hasLemmaStmt : Bool
  hasVerifierArtifact : Bool
  hasCertificateScope : Bool
deriving DecidableEq

def isPlaceholder (i : CertifierInput) : Bool :=
  match i.kind with
  | InputKind.missing => true
  | InputKind.perContract => true
  | InputKind.concrete => false

def unresolved (i : CertifierInput) : Bool :=
  isPlaceholder i || !i.hasLemmaStmt || !i.hasVerifierArtifact || !i.hasCertificateScope

def certify (i : CertifierInput) : Verdict :=
  if unresolved i = true then Verdict.aborted else Verdict.certified i.claim

theorem msl_erdos507_lem_r005_r005_composition (i : CertifierInput) : ((isPlaceholder i = true → unresolved i = true) ∧ (i.hasLemmaStmt = false → unresolved i = true) ∧ (i.hasVerifierArtifact = false → unresolved i = true) ∧ (i.hasCertificateScope = false → unresolved i = true) ∧ (unresolved i = true → certify i = Verdict.aborted) ∧ (∀ (c : Claim), Verdict.aborted ≠ Verdict.certified c)) → (isPlaceholder i = true → i.hasLemmaStmt = false → i.hasVerifierArtifact = false → i.hasCertificateScope = false → certify i = Verdict.aborted ∧ ∀ (c : Claim), certify i ≠ Verdict.certified c) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos507_lem_r005_r005_composition
