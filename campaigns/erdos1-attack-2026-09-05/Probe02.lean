import Mathlib

/-!
PROBE 02 — how far can the kernel push?
  Q1  Conway-Guy at n = 11 (max 594, ratio 0.29004) -- 2048 subsets, ~4.2M dedup comparisons
  Q2  Conway-Guy at n = 12 (max 1164, ratio 0.28418) -- 4096 subsets, ~16.8M comparisons
  Q3  can `Finset.powersetCard 6 (Finset.Icc 1 23)` (100,947 sets) be exhausted? -> least_N_6 = 24
Each is a strictly optional STRENGTHENING of Attack01; a timeout here costs nothing.
-/

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

theorem probe_q1 :
    ((({285,433,510,550,570,581,587,590,592,593,594} : Finset ℕ)).powerset.image
      (fun S => S.sum id)).card = 2048 := by
  decide

theorem probe_q2 :
    ((({570,855,1003,1080,1120,1140,1151,1157,1160,1162,1163,1164} : Finset ℕ)).powerset.image
      (fun S => S.sum id)).card = 4096 := by
  decide

theorem probe_q3 :
    ((Finset.powersetCard 6 (Finset.Icc 1 23)).filter
      (fun A => (A.powerset.image (fun S => S.sum id)).card = 64)) = ∅ := by
  decide

#print axioms probe_q1
#print axioms probe_q2
#print axioms probe_q3
