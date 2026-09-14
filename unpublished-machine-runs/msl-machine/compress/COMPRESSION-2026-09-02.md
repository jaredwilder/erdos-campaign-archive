# COMPRESSION REPORT 2026-09-02

**The organ that climbs.** COMBINE / COMPRESS / RISE / LADDER.

⛔ Nothing in this report is proved. There is no Lean on this machine tonight, so every kernel job below is FILED and every verdict is `KERNEL_NOT_RUN`. A candidate that cleared all six gates is a candidate.

| problem | proved leaves | unused | targets | headline NC | headline leaves | free chains | free decomp | lifts | model | jobs | proved T | lateral | height | ratio | dist before→after |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| erdos289 | 21 | 16 | 8 | 0 | 0 | 0 | 0 | 0 | 9 | 18 | 0 | 1 | 0 | 0.0 | 2→2 |
| erdos479 | 26 | 23 | 5 | 0 | 0 | 0 | 0 | 0 | 9 | 16 | 0 | 0 | 0 | 0.0 | 2→2 |
| erdos936 | 23 | 21 | 2 | 0 | 0 | 0 | 0 | 0 | 6 | 12 | 0 | 1 | 0 | 0.0 | 2→2 |

## Totals

- `chain_jobs_filed_free`: **0**
- `decomposer_compositions_free`: **0**
- `directed_lifts_proposed`: **0**
- `gate:G1_SCHEMA`: **1**
- `headline_kernel_verified_leaves`: **0**
- `headline_killed_constraints`: **0**
- `headline_near_close_targets`: **0**
- `kernel_jobs_filed`: **46**
- `killed_restatements_refused`: **0**
- `lateral_kept`: **2**
- `leaves_proved`: **70**
- `leaves_proved_and_unused`: **60**
- `model_candidates`: **24**
- `proved_T`: **0**

## Spend

```
{
 "cap_usd": 0.5,
 "spent_usd": 0.018237,
 "calls": 24,
 "calls_with_reported_cost": 24,
 "reserve_per_call_usd": 0.01
}
```

## The candidate table

### erdos289
| T | origin | status | rise | gate stop | discharges |
|---|---|---|---|---|---|
| `erdos289_one_sixth_interval_reaches_beyond_sixty` | PROPOSER | OPEN | RISE | - | erdos289:BRANCH_A |
| `W4_two_interval_fragment` | PROPOSER | OPEN | RISE | - | erdos289:BRANCH_A |
| `erdos289_bridge_head_tail` | PROPOSER | OPEN | RISE | - | erdos289:BRANCH_A |
| `sq_le_sq_iff_abs_le_of_nonneg` | PROPOSER | OPEN | RISE | - | erdos289:FLEAF:987cb071355b04164228:7 |
| `runSum_eq_iff_nat_eq` | PROPOSER | OPEN | RISE | - | erdos289:FLEAF:987cb071355b04164228:7 |
| `l1_bridge_curry` | PROPOSER | OPEN | RISE | - | erdos289:FLEAF:987cb071355b04164228:7 |
| `L1_no_sixth_from_two` | PROPOSER | OPEN | LATERAL | - | erdos289:FLEAF:987cb071355b04164228:8 (check_l1_fragment = true) |
| `runSum_2_4_exceeds_one` | PROPOSER | OPEN | RISE | - | erdos289:FLEAF:987cb071355b04164228:8 |
| `W4_nat_fragment_gen` | PROPOSER | OPEN | RISE | - | erdos289:FLEAF:987cb071355b04164228:8 |

### erdos479
| T | origin | status | rise | gate stop | discharges |
|---|---|---|---|---|---|
| `erdos479_k_neg_one_inf` | PROPOSER | OPEN | RISE | - | erdos479:BRANCH_A |
| `erdos479_family_odd_generalized` | PROPOSER | OPEN | RISE | - | erdos479:BRANCH_A |
| `erdos479_affirmative_bridge` | PROPOSER | OPEN | RISE | - | erdos479:BRANCH_A |
| `erdos479_k3_no_witness_range` | PROPOSER | OPEN | RISE | - | erdos479:BRANCH_B |
| `erdos479_witness_structure` | PROPOSER | OPEN | RISE | - | erdos479:BRANCH_B |
| `erdos479_witness_lift` | PROPOSER | OPEN | RISE | - | erdos479:BRANCH_B |
| `check_l1_fragment_range_six` | PROPOSER | REFUSED | - | G1_SCHEMA | erdos479:FLEAF:2ded7584a23fc4ffed6d:5 |
| `erdos479_witness_family_all_s` | PROPOSER | OPEN | RISE | - | erdos479:FLEAF:2ded7584a23fc4ffed6d:5 |
| `check_l1_fragment_bridge` | PROPOSER | OPEN | RISE | - | erdos479:FLEAF:2ded7584a23fc4ffed6d:5 |

### erdos936
| T | origin | status | rise | gate stop | discharges |
|---|---|---|---|---|---|
| `erdos936_period_all_k` | PROPOSER | OPEN | RISE | - | erdos936:BRANCH_A |
| `erdos936_three_adic_lifting` | PROPOSER | OPEN | RISE | - | erdos936:BRANCH_A |
| `erdos936_81_dvd_iff` | PROPOSER | OPEN | RISE | - | erdos936:BRANCH_A |
| `erdos936_odd_not_mult3_not_powerful` | PROPOSER | OPEN | LATERAL | - | erdos936:DEMAND:R002:L1:1 (shrinks: eliminates every odd n with 3 ∤ n from the squared-exponent demand for 2^n + 1) |
| `erdos936_period_divisor_of_63` | PROPOSER | OPEN | RISE | - | erdos936:DEMAND:R002:L1:1 |
| `erdos936_powerful_odd_to_mod6_3` | PROPOSER | OPEN | RISE | - | erdos936:DEMAND:R002:L1:1 |

