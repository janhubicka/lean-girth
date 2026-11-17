# Track 4 — q=2 ordered-partiteness obstruction in the current Lean interface

**16 November 2026. STATUS: mathematical counterexample to a proposed inference; no Lean compilation or counterexample formalization.** Applies to the **full relational order expansion** \`L.withOrder\` used in several current Lean modules, not automatically to the circulation manuscript's unordered one-edge language with auxiliary within-part orders.

## Explicit three-edge example

Let \`A\` be the three-vertex, 3-uniform edge with three fine parts numbered 1<2<3. Let the vertex set be \`{x1,y1}\` in part 1, \`{x2,y2}\` in part 2 and \`{x3,y3}\` in part 3. Take exactly the physical edges

- e12 = {x1,x2,y3};
- e23 = {y1,x2,x3};
- e13 = {x1,y2,x3}.

Each is a transversal copy of the **same** 3-edge type, and the pairwise edge intersections are exactly \`{x2}\`, \`{x3}\`, \`{x1}\` respectively. The support is linear and has Berge girth **3**, hence girth **>2**. A height-one train with bottom equality and universal top satisfies the q=2 labelled wagon-girth requirement.

In the \`L.withOrder\` relational expansion, orient each edge by its fine parts, so each of its three vertex pairs supplies the corresponding binary order relation. Thus in the induced set \`S={x1,x2,x3}\` we have x1<x2, x2<x3 and x1<x3, **but S is not a physical 3-edge**. Every two members of S occur together in the binary order relation, so S is irreducible. Its part-map image is the entire ordered 3-edge A, where the ternary edge does hold. Therefore the natural fine-part map **fails reflection on an irreducible induced substructure** and is NOT \`IsHomomorphismEmbedding\` into the ordered A. In particular, \`H.IsPartiteOver A.ordered\` does not follow from the q=2 coloured-edge-type and forest hypotheses.

The same obstruction persists inside an induced selected copy of this target. It does not rely on selected-copy duplication, on a missing A-edge, or on the generic nine-vertex K4 graph example from the prior audit.

## Important scope distinction

When the auxiliary order is **not part of the relational language**, the induced set S above has no internal 3-ary hyperedge and is reducible. In the unordered one-edge hypergraph reduct, the fine-part projection is a homomorphism-embedding: an irreducible induced subhypergraph with at least two vertices must occupy distinct fine parts and must be a full physical edge. Thus this example does **not** refute the paper's F_2 assertion, the abstract F_2=>R_2 conversion, or the ordinary unordered partite projection.

The issue is a *representation mismatch*: the current raw witness module \`TrainCoverageFreeRawFtWitness.lean\` requests \`core.IsPartiteOver A0.ordered\`, and \`TrainCoverageFreeDirectPartiteFtStep.lean\` uses it to discharge the attachment's \`corePartite : Core.IsPartiteOver D\`. An arbitrary F_2 witness does NOT automatically supply the ordered version. Its exact hPartite premise therefore remains an **extra assumption**. The new \`initialStrongTrainRamsey_of_rawFtWitnesses\` is a valid conditional proof *if* that premise is available but does not yet establish the unconditional forest-to-order proposition.

## Repair options

1. **Preferred:** formulate the actual F_t witness and the local physical attachment on the **unordered hypergraph reduct** with fine-part predicates, and transport the auxiliary within-part orders separately. Use the original induction's order-extension observation only after the attachment/final finite pass. Keep the full selected physical edges, mixed forests, train labels, parameters and positive bounds. Prove the unordered \`IsPartiteOver\` from the single coloured-edge type. This is a representation-specific repair, not a new combinatorial Ramsey assumption.
2. If the ordered Lean representation must be retained, prove an **order-reduct transfer** for the existing attachment and stage structures that uses only the ordered source to identify physical copies (rigidity), but not to enforce \`IsHomomorphismEmbedding\` into \`A0.ordered\` on ambient irreducibles. Do not merely add an unproved hPartite axiom.
3. A construction of a specially ordered output avoiding every such false irreducible image is NOT a general solution: the target above is already a legal q=2 train and the selected target copy is induced.

## Work completed this turn

- Added five source-only coverage-free modules (selected lower bundle, selected positive transfer, direct raw partite step, raw-witness structure and conditional global finite pass).
- Added their imports and eight \`#print axioms\` registrations to \`CheckTrack4MinimumOwnerSwap.lean\`, now 198 registrations, **none run**.
- Corrected the raw-bridge module documentation to acknowledge the extra ordered \`IsPartiteOver\` field.
- The original cycle-preservation branch remains unaffected by this obstruction.
- No manuscript validation mark is promoted and no Lean kernel correctness claim is made.

**Next mathematical verification:** explicitly check whether the original paper proof of the direct local F_t attachment uses only the unordered partite projection. If so, state the unordered projection observation in the preparation section; then formalize the order-forgetful attachment interface. This is the decisive q=2 gap, not a desire for stronger forest coverage.


## 17 November adversarial strengthening: the issue affects stage partiteness too

The failure is potentially more basic than the six-vertex q=2 example. The
existing `TrainCoverageFreeForestStage.lean` defines
`ForestStage.system : Partite.System L P Vertex` together with
`isPartite : system.IsPartiteOver D`; in the conversion this is instantiated
with `L.withOrder` and `D : RelStructure L.withOrder P`. The local
`RawPartiteFtWitness` similarly requires `core.IsPartiteOver A₀.ordered`.

**Conditional elementary obstruction (check the precise library semantics).**
If `L.withOrder` includes the full strict total order on *all* vertices, and
`IsPartiteOver` requires the part map to preserve that relation, then
the part map must be injective: for two distinct vertices `x,y` in the
same part, exactly one of `x<y` or `y<x` holds in the core, while their
images coincide, contradicting irreflexivity of the target order. Thus a
nontrivial blow-up with multiple vertices in any part cannot satisfy the
ordered `IsPartiteOver` predicate at all. The library theorem
`ordered_hereditarilyIrreducible` is consistent with this concern. This
argument is independent of q and does not require the 3-edge example.
It extends the audit target to the **old coverage-free stage**, its initial
construction and any generic ordered `Partite.System`, not only raw F_t.

Before replacing any theorem, inspect the actual definition of
`RelStructure.ordered`, the `L.withOrder` relation and
`IsHomomorphismEmbedding`: if the order is instead represented only as
fibrewise auxiliary data, the preceding injectivity argument does not
apply. No kernel evidence has yet settled this implementation question.

**Minimal representation repair if the order is indeed global:** keep the
partite projection and EHN geometry on the unordered physical language
`L` (with vertex-part colours), and put compatible order data on
the separately chosen vertices in each fine part. Preserve those orders
along picture embeddings and form the coarse order only at the end.
Do not silently drop global order on existing copies or assert that an
arbitrary order-expanded relational embedding is partite. The local
`F_t` data and the selected physical edge arrow must be transported
across this representation boundary.

Status: mathematical conditional no-go and source-level audit only.
It has not been compiled or promoted to a theorem. Existing manuscript
validation marks remain OPEN.
