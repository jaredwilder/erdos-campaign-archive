# Running the independent verifier

`receipts/xverify.py` re-checks a claimed cover **from the definition**. It shares no code with the
C decider that produced the receipts: it reads their JSON, expands every block into its pairs, and
asks whether all 66 pairs of a 12-set are covered.

It takes the receipt file as an argument, which was previously undocumented:

```
python xverify.py c9b.json
```

## All four receipts, re-run 2026-09-10

| receipt | blocks | covers all 66 pairs | note |
|---|---|---|---|
| `c8.json` | 8 | **no** | missing the pairs (9,11) and (10,11) |
| `c8b.json` | - | - | `EXHAUSTED_NO_COVER` after **4,112,326,321 search nodes** |
| `c9b.json` | 9 | **yes** | |
| `c10.json` | 10 | **yes** | |

Every invocation exits 0. Exit 0 means *the verifier ran*, not *the cover is good* - the verdict is
in `covers_all_66_pairs`.

## The row that matters is the first one

`c8.json` is a claimed object that the verifier **rejects**, naming the two specific pairs it fails
to cover. A verifier that only ever agrees is indistinguishable from a verifier that does nothing.
This one says no when the answer is no, and it says which pairs.

Taken together the four rows give C(12,5,2) = 9: the 8-block search is exhausted without a cover,
and a 9-block cover is confirmed from the definition.

## What is not claimed

The exhaustion is a search result over the space the decider enumerates. It is a bound with a
ceiling, not a proof-assistant theorem, and nothing here is kernel-sealed.
