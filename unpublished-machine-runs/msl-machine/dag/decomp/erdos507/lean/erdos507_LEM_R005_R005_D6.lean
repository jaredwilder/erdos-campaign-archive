import Mathlib

set_option autoImplicit false
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

theorem msl_erdos507_lem_r005_r005_c6 (c : Claim) : Verdict.aborted ≠ Verdict.certified c := by sorry
