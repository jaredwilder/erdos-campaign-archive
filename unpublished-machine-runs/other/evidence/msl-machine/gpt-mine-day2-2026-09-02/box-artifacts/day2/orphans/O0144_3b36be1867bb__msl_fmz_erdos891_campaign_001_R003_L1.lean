import Mathlib

set_option autoImplicit false


structure PacketRecord where
  reduction : String
  residual : String
  transferShas : List String

def forbiddenBodies : List String :=
  ["kernel body", "witness body"]

def vl1Verifier (p : PacketRecord) : Bool :=
  (p.reduction == "none")
  && (p.residual == "per contract")
  && (p.transferShas.length == 6)
  && ((p.transferShas.eraseDups).length == 6)
  && (p.transferShas.all (fun s => !(forbiddenBodies.contains s)))

def r003 : PacketRecord :=
  { reduction := "none"
    residual := "per contract"
    transferShas := ["sha_foreign_01", "sha_foreign_02", "sha_foreign_03",
                     "sha_foreign_04", "sha_foreign_05", "sha_foreign_06"] }

theorem msl_fmz_erdos891_campaign_001_R003_L1  : vl1Verifier r003 = true := by decide

-- axiom footprint
#print axioms forbiddenBodies
#print axioms vl1Verifier
#print axioms r003
#print axioms msl_fmz_erdos891_campaign_001_R003_L1
