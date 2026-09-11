# Erdős 595 — the barrier tower (MSL epoch 13, absolute rounds 218–236)

**Target, frozen:** *Is there an infinite graph `G` which contains no `K4` and is not the union of
countably many triangle-free graphs?* Contract sha256
`7a511a911acc0ece511b59d5048818b5073983519f93103d6c1dbe79da8eb794`
(`../erdos595-campaign-001/contract.json`).

**Status: NOT CLOSED.** No witness constructed, no refutation proved. What this run produced is a
kernel-sealed tower of necessary conditions on any witness, plus the algebra of the class it must
escape.

Every artifact below: Lean 4 v4.31.0-rc1, `lake env lean` exit 0, **zero `sorry`**, axiom footprint
exactly `{propext, Classical.choice, Quot.sound}`. Machine-readable audit with per-file sha256:
`INDEX.json` (18 files, 0 unclean).

## The picture, in one paragraph

**Every graph on at most continuum-many vertices is coverable** (`coverable_of_continuum_colouring`:
inject the vertices into Cantor space, colour each edge by the least coordinate where its endpoints
differ; three sequences cannot pairwise differ at one fixed coordinate). **Non-coverable graphs
begin exactly at 𝔠⁺**, where Erdős–Rado forces a monochromatic triangle in every countable
colouring of the pairs — so the complete graph on 𝔠⁺ is not coverable, and the Δ-colouring above
witnesses that this threshold is sharp. Erdős 595 therefore asks precisely: **does the phenomenon
that begins at 𝔠⁺ survive deleting every K₄?** Every source of non-coverability the estate can
name runs through large complete subgraphs, which is exactly what the hypothesis removes. Two
further floors: the least witness size has **uncountable cofinality** (a countable-cofinality
cardinal splits into countably many smaller parts, and `coverable_of_coverable_parts` reassembles
their covers), and a witness lives inside **one connected component**
(`coverable_of_blocks` — coverability survives disjoint unions of *arbitrary* size).

## Where the problem actually stands after this run (rounds 237–243)

Three prior-art facts, each with a receipt on disk, reshaped the target:

1. **The finite analogue is solved.** `ErdosProblems/595.lean` records
   `erdos_595.variants.folkman_finite` (category *research solved*): for every finite `n` there is a
   finite K4-free graph not coverable by `n` triangle-free graphs — Folkman [Fo70], Nešetřil–Rödl
   [NeRo75]. **The obvious lift is dead:** any countable amalgam of finite graphs has a countable
   edge set, hence is coverable outright by `coverable_of_countable_edgeSet`. A witness cannot be
   assembled from the Folkman family over a countable index.
2. **Linearity is not a barrier.** `cover_iff_colouring` plus
   `two_triangles_share_at_most_one_edge` make the target equivalent to *uncountable chromatic
   number for the triangle hypergraph, which is always a linear 3-uniform system*. Erdős–Hajnal–
   Rothschild already give an **uncountably chromatic linear 3-uniform system** (reported in
   Reiher, *Obligatory hypergraphs*, arXiv:2403.11223 §1 — snapshot at
   `../erdos593-close-2026-09-05/receipts/reiher-2403.11223-snapshot-2026-09-05.txt`). So the
   reframing does not decide the problem, and the hope attached to it was retracted at round 242.
3. **What is left is realizability.** The whole remaining content: *can an uncountably chromatic
   linear triple system be realized as the triangle hypergraph of a K4-free graph?*
   `link_map` seals the local necessary condition — at every point, the hyperedges through it are
   indexed injectively by an **independent** set of the realizing graph.

One further unifying theorem landed: `coverable_of_hom` — **coverability pulls back along graph
homomorphisms**. Six of the earlier colouring-shaped conditions are instances of it (a proper
colouring is a homomorphism into a complete graph, and complete graphs on ≤ ℵ₁ points are
coverable). Its contrapositive is the sharpest necessary condition in the file: **a witness admits
no homomorphism into any coverable graph**, hence none into any graph of size ≤ ℵ₁.

**Prior-art collision, recorded:** two of the sealed theorems duplicate corpus declarations of
category *textbook* — `coverable_of_le` is `erdos_595.variants.subgraph_of_countable_union`, and the
star decomposition appears in the same file. The other sixteen have no corpus counterpart.
Novelty beyond that is **UNVERIFIED**: the estate's `noveltyforge acquire` returned 30 rows keyed on
the domain phrase and missed all three of the references the corpus file itself names — a retrieval
failure, not a finding of absence.

## The definition, bound to the source

`Coverable G := ∃ H : ℕ → SimpleGraph V, (∀ n, H n ≤ G) ∧ (∀ n, (H n).CliqueFree 3) ∧
G.edgeSet ⊆ ⋃ n, (H n).edgeSet`

`coverable_iff_source` proves this equivalent to the source's own phrasing — a countable family of
triangle-free graphs on the same vertex type whose edge sets union to **exactly** `G.edgeSet`, with
no subgraph hypothesis. This is what moves the semantic-binding court off `UNKNOWN_BINDING`.

## Sufficient conditions for coverability (each kills a family of candidate witnesses)

| theorem | a graph is coverable if … |
|---|---|
| `coverable_of_countable_edgeSet` | its edge set is countable |
| `coverable_of_colouring` | it has a countable edge colouring with no monochromatic triangle (**equivalence**, `cover_iff_colouring`) |
| `coverable_of_continuum_colouring` | it is properly vertex-coloured by the Cantor space — i.e. chromatic number ≤ 𝔠, via the least-differing-coordinate colouring |
| `coverable_of_backDegree` | its vertices are linearly ordered with each vertex's predecessors injectively indexed by ℕ — hence **every graph of size ≤ ℵ₁ is coverable**, with no chromatic or clique hypothesis at all |
| `coverable_of_local_colouring` | (weakening of the above) each vertex's *lower neighbourhood* induces a countably-chromatic graph |
| `coverable_of_countable_hitting_set` | some countable **vertex** set meets every triangle |
| `coverable_of_countable_edge_transversal` | some countable **edge** set meets every triangle |

## The algebra of the coverable class

`coverable_iUnion` (closed under countable unions of subgraphs) and `coverable_of_le` (closed
downward) make the coverable graphs a **countably complete ideal in the subgraph order**. So the
target asks exactly whether some K4-free graph lies outside that ideal, and a witness is
*indecomposable*: not a countable union of coverable pieces.

## Necessary conditions on a witness (the contrapositives)

Uncountably many edges; no proper vertex colouring by ℕ (`witness_necessary`); chromatic number
**strictly above the continuum**; more than ℵ₁ vertices; no countable vertex transversal of its
triangles; no countable edge transversal; and under **every** linear ordering, some vertex whose
lower neighbourhood has uncountable chromatic number.

## Two findings worth flagging

1. **Route killed by theorem.** The apex construction — a triangle-free base of huge chromatic
   number plus apex vertices — is dead. Any construction with countably many apexes has a countable
   triangle transversal, so `coverable_of_countable_hitting_set` covers it outright.
2. **The tower did not use K4-freeness.** Audited at round 235: thirteen of the fifteen sealed
   theorems prove coverability from hypotheses available to *every* graph. `link_independent` /
   `no_triangle_in_neighborhood` (round 235) is the first sealed statement that consumes
   `CliqueFree 4` — the common neighbourhood of an edge is independent, equivalently every
   neighbourhood induces a triangle-free graph. The join of that fact to
   `coverable_of_local_colouring` is where the target's own hypothesis first does work, and it is
   the open front.
3. **Independence probe.** `exists_free_triangle`: over an uncountable vertex type no countable edge
   set meets every triple. So the complete graph on ℵ₁ vertices defeats the edge-transversal
   condition — and is still coverable by `coverable_of_backDegree`. Defeating one barrier is cheap;
   the barriers are not jointly close to sufficient.

## Explicitly UNPROVED

The problem itself, in both directions. No witness; no proof that every K4-free graph is coverable.
The source's own trap list is respected: uncountable chromatic number alone does **not** prove
failure of a countable triangle-free edge cover, and nothing here claims it does.

## Closure properties of the coverable class (the algebra, all kernel-sealed)

| theorem | coverability is preserved by … |
|---|---|
| `coverable_of_le` | passing to a subgraph — so the class is a **downward-closed ideal** |
| `coverable_iUnion` | **countable** unions of subgraphs |
| `coverable_of_blocks` | disjoint unions of **arbitrary** size (blocks indexed by any type) |
| `coverable_of_hom` | **pullback along any graph homomorphism** — six of the colouring-shaped conditions are instances of this one |
| `coverable_of_coverable_parts` | **countable vertex partitions with coverable parts**, whatever the crossing edges do |
| `coverable_add_vertex` | adding one vertex — so failure can only appear at a limit of uncountable cofinality |

Consequently a witness is *indecomposable* in a very strong sense: connected, not a countable union
of coverable subgraphs, not a countable vertex-partition into coverable parts, admitting no
homomorphism into any coverable graph, and of size > 𝔠 with uncountable cofinality.

## The open front

Whether the Erdős–Rado phenomenon at 𝔠⁺ has a K₄-free host — equivalently (both directions
kernel-sealed) whether an uncountably chromatic **linear** triple system with **independent links**
is realizable as the triangle hypergraph of a K₄-free graph. Uncountably chromatic linear triple
systems do exist (Erdős–Hajnal–Rothschild), so linearity is no barrier; realizability is the whole
remaining question. The estate could not reach the explicit EHR construction — `noveltyforge` misses
it — so that is the standing external request.
