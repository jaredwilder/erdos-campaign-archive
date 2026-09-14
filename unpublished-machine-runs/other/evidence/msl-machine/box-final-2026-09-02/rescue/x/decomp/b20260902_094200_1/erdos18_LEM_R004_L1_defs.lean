import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def certPassed (b : Bool) : Prop := b = true

def verifierRefutes (P : Prop) [inst : Decidable P] : Prop := decide P = false
