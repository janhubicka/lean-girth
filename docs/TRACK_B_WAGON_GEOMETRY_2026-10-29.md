# Track B: generated output-wagon geometry

This work starts the audited Track B contract in issue #661, using the common
base `3af405cc3a51ca7d3201e221a8a2a56d2e443751`. The scope and exclusions come
from coordinator #664 and audit PR #665. Only the circulation argument is
addressed. The manuscript, root imports, shared workflow and other lanes are
not edited here.

## New interfaces

The new theorems concern **actual physical A-support edges and the quotient
parents of the generated attachment**. Neither output `LinearPretrain` nor
Track A's cycle-transfer conclusion is assumed.

| Module | Interface | Inputs and scope |
|---|---|---|
| `TrainSelectedPictureWagonPairGeometry` | `attachedSelectedPicture_same_standard_blocks_parent_eq` | Old wagon linearity and exact standard restriction identify the output parents of two edge blocks in one standard through distinct common vertices. |
| same | `attachedSelectedPicture_parent_eq_of_standard_pair` | Whole-standard A-strongness absorbs an ambient pair edge, after which old wagon linearity determines its generated parent. |
| same | `attachedSelectedPicture_standard_blocks_parent_eq` | Old/core full order-two bounds, shared compatibility and whole gluing-image strongness identify parents of blocks in arbitrary two standards. The actual-picture instantiation also retains finite A, partiteness over the base, base A-linearity/rigidity and strong designated base copies. The standard indices may coincide and physical edges may repeat. |
| same | `attachedSelectedPicture_standard_wagon_carriers_inter_subsingleton` | Complete **source** wagon carriers with different generated output labels intersect in at most one vertex. This is not yet the corresponding statement about complete generated wagon carriers. |
| `TrainSelectedPictureCorePairGeometry` | `actualASupport_core_edge_pullback` | Every actual support edge contained in the core is the canonical physical image of a genuine core edge. |
| same | `generatedActualASupportTrain_coreWagon_pair_absorbs_edge` | A-strongness of the active subsystem, core wagon linearity and shared-relation preservation give pair-edge absorption by the generated image of a core wagon. |
| same | `generatedActualASupportTrain_parent_eq_of_core_pair` | The same absorption conclusion starts from arbitrary actual edge witnesses contained in the core, preserving their original output parent. |
| same | `generatedActualASupportTrain_core_blocks_parent_eq` | Two core-local edge blocks through a common distinct pair have equal output parents. This needs core wagon linearity and exact core restriction, but no strongness or pair-edge-existence premise. |
| `TrainSelectedPictureMixedPairGeometry` | `sharedWitness_copy_wagon_pair_shared_edges` | The existing three-occurrence long probe supplies genuine shared edges through both endpoints in a specified core wagon when no pair edge exists. |
| same | `attachedSelectedPicture_standard_core_blocks_parent_eq` | A standard-local block and a core-local block through the same distinct pair have equal output parents. It needs old linearity, the core full order-two bound and strongness of the chosen standard; no old supreme-cycle bound or finite-A assumption is added. |

## How the proofs use the recovered formalization

For two different standards, the proof invokes the existing mixed contained-block
obstruction in `TrainSelectedPictureContainedBlocks` with genuine physical edge
labels. If their output parents were different, it would supply a core edge
through the two boundary vertices. Whole-standard strongness pulls that same
physical edge into both standards. Exact restriction and **old** wagon linearity
then identify its parent with both blocks, giving the contradiction. The
same-standard case needs no cycle bound.

The mixed core/standard case separates pair-edge existence from its negation.
In the pair-edge branch, standard absorption and core-local linearity suffice.
In the no-pair branch, `copy_long_piece_of_two_edge_probe` is legitimately
applicable in the core witness. Its long piece supplies shared source edges;
`longPiece_edges_in_given_wagon` retains the specified core wagon. Actual
shared-edge identities and exact restriction bring these edges into the old
standard, where old wagon linearity finishes the proof.

Only this no-pair branch invokes the acceptable three-occurrence probe. The
auxiliary three-edge configuration containing an ambient pair edge is never
declared acceptable. Nor is global replacement legality inferred from local
piece validity: only the individual shared edge witnesses are needed here.

## Continuation: crossing wagons and complete off-core carriers

The continuation removes the source-piece localization premise for pairs of
vertices **both outside the core**. Its new interfaces are:

| Module | Interface | Inputs and scope |
|---|---|---|
| `TrainSelectedPictureCrossStandardWagons` | `generatedActualASupportTrain_cross_standard_wagon_unique` | For distinct standards i,j, at most one generated output wagon contains physical edges from both. Requires exact shared compatibility and the core `LocalPieceSystemBound 2`; no source/output linearity, strongness, finite support or endpoint incidence is assumed. |
| `TrainSelectedPictureOffCorePairGeometry` | `actualASupport_offCore_incident_edges_same_standard` | Any two actual support edges incident with one off-core vertex have a common standard owner. This follows from exhaustive physical edge coverage and free attachment geometry; no train or wagon premise is used. |
| same | `attachedSelectedPicture_offCore_blocks_parent_eq` | Arbitrary physical endpoint blocks through a distinct off-core pair have equal generated parents, using old `LinearPretrain`, core `LocalPieceSystemBound 2` and exact shared compatibility. |
| same | `attachedSelectedPicture_offCore_wagon_eq_of_common_vertex_pair` | The same uniqueness for complete `WagonVertex` membership, with no preselected endpoint edges or source standards. |
| same | `attachedSelectedPicture_offCore_wagon_class_eq_of_common_vertex_pair` | Direct formulation for the complete generated `wagonClassCarrier` sets and their actual quotient labels. |
| same | `attachedSelectedPicture_offCore_wagon_carriers_inter_subsingleton` | For distinct output wagons, the intersection of their complete carriers **outside the core** is a subsingleton. Their intersection inside the core remains unrestricted by this theorem. |
| same | `attachedSelectedPicture_parent_eq_of_offCore_pair` | An ambient actual edge meeting a generated wagon at two distinct off-core vertices has that wagon's parent. This is restricted pair-edge absorption without output linearity or strongness as an input. |

The crossing-wagon proof uses
`generatedActualASupportTrain_cross_standard_copy_local_incidence` to obtain
genuine shared edges in each prescribed witness copy. The existing
`generatedActualASupportTrain_standard_parent_eq_coreEmbedding` identifies
each original output parent with the image of its core ancestor. Two distinct
output parents would therefore produce two distinct core wagons meeting both
distinct witness labels, contrary to
`OrderOneData.no_two_designated_meet_two_wagons`.

For the off-core pair, the actual edge equivalence transports
`physicalPictureEdge_covered` to every actual support edge. Core edges are
excluded at an off-core vertex; standard-copy intersections force all its
incident edges into the same standard. The two endpoint owners either agree,
when old wagon linearity applies, or differ, when crossing-wagon uniqueness
applies. No localization of the original wagon is assumed. In particular,
this proof does not confuse uniqueness of representations of a **single**
private edge with ownership of **different** incident edges.

## Core incidence and the first mixed core/off-core case

Three further modules preserve the actual wagon parent when bringing a
core vertex into a chosen standard:

| Module | Main interface | Inputs and scope |
|---|---|---|
| `TrainSelectedPictureCoreVertexLocalization` | `generatedActualASupportTrain_two_standard_vertex_shared_witnesses` | Two standard edges in the **same** generated wagon, through the **same** vertex and with distinct standard indices, yield shared representatives through that vertex in both standards. Their original old relations and output parent are retained. Uses active-support coverage and the core order-one `Bound`, without source/output linearity or strongness. |
| same | `generatedActualASupportTrain_two_standard_vertex_core_edge` | Extracts a genuine core support edge whose actual image contains the specified vertex and has the specified original output parent. |
| `TrainTwoWagonVertexProbe` | `OrderOneData.copy_bridges_of_common_wagon_vertex` | Under `LocalPieceSystemBound 2`, a designated copy meeting two distinct wagons has a bridge in each through any common wagon vertex. The vertex need not previously be known to lie in the copy. The module also checks the actual probe, its order, full acceptability, the edge-witness version and a carrier-membership corollary with explicit edge-carrier containment. |
| `TrainSelectedPictureCoreOffCorePairGeometry` | `attachedSelectedPicture_core_offCore_blocks_parent_eq` | Two generated wagons sharing an off-core vertex and a vertex with **genuine core-edge witnesses in both wagons** have equal parents. Uses old `LinearPretrain`, core `LocalPieceSystemBound 2` and exact shared compatibility; no core/output linearity or strongness is assumed. |

For the two-standard localization theorem, intersection geometry and active
coverage first put the vertex in both **prescribed** shared witness copies.
Only then is `OrderOneData.both_bridges` applied to the core ancestor supplied
by the actual cross-standard relation. New shared representatives are reflected
back through exact compatibility, and the quotient bridge preserves the
original output parent. Meeting another standard somewhere else would not
provide the required two-source vertex premise.

The two-wagon probe has labels `[copy i, edge a, edge b]` and connectors
`[wagon p, vertex x, wagon q]`, with `p ≠ q`. It has twice-order four. The sole
vertex position is adjacent to both wagon positions; each wagon also has a
wagon neighbor, so A2's two-vertex ambient-nonedge clause has impossible
premises. A3 is supported on that single vertex position. Thus all A1--A3
conditions are proved directly, with no ambient pair-edge prohibition.
The only designated occurrence is the copy, whose two mixed replacements
give genuine bridge edges in the two specified wagons. This uses necessary
local replacement pieces and does not infer global replacement legality.

In the actual mixed application, the off-core endpoint gives a common
standard owner. Standard/core incidence shows that its witness copy meets
both core ancestors, while the supplied core edges place the other endpoint
in both ancestors. The probe brings both parent-labelled incidences into the
chosen standard, where old wagon linearity finishes the comparison.

## Adversarial scope checks

- Every linearity input belongs to the old train or the core witness.
- An ambient edge is pulled back only after strongness of the **entire**
  containing standard or core has been established.
- Quotient labels are identified by actual edge relations and quotient maps,
  never by equality of vertex-carrier sets.
- Designated-copy vertex incidence and wagon incidence are not conflated:
  `Meets F W` and `x ∈ carrier F` need not put `x` in `W`. The final block
  equalities use physical edge witnesses at the stated endpoints.
- Empty or singleton A, coincident standard indices, repeated edge witnesses
  and a pair edge coinciding with a block edge introduce no extra assumptions.

The finite diagnostic `scripts/check_track_b_wagon_geometry.py` checks 4,207
localized incidence models, including 1,009 whose output wagon family is not
linear. It also checks concrete failures when whole-piece strongness or exact
restriction reflection is omitted. Constituent-edge strongness does not repair
the first failure. These are finite incidence diagnostics, not realizations of
all relational hypotheses or substitutes for the Lean kernel checks.

The additional `scripts/check_track_b_off_core_geometry.py` checks 20,382
finite incidence models (20,366 nonempty), including 6,138 with nonlinear
complete output wagon families and 2,112 with mixed core/off-core overlap.
It checks complete carriers and contains separate countermodels for removing
source wagon linearity, off-core owner uniqueness or crossing-wagon control.
Its mixed-pair example satisfies those three downstream interfaces, showing
their precise limitation. These are not counterexamples satisfying the full
relational attachment and system-girth hypotheses.

## Remaining Track B obligation

The source-local results cover all three combinations: standard/standard,
core/core and standard/core. The continuation additionally covers arbitrary
generated wagon pairs when both common vertices lie outside the core.
The mixed core/off-core case is also proved when both wagon incidences at the
core endpoint have actual core representatives. The two-standard localization
theorem supplies such a representative when one wagon reaches that vertex
through distinct standards. Arbitrary core/off-core pairs and arbitrary
core/core pairs still need further arguments. Merely finding a shared edge
through a core vertex does not preserve the required original wagon parent.

A genuine single-source obstruction remains: a private old wagon can touch
the active subsystem in one vertex without containing a shared edge. Thus
unconditional core localization of every generated-wagon vertex is not a
valid intermediate target. A useful incidence dichotomy is to retain either
a genuine same-parent core edge at the vertex or its unique standard owner.

The next concrete target is the **fully arbitrary core/off-core pair**. A
reviewed route generalizes the checked probe from two actual edge labels to
two arbitrary source labels a,b: use `[hub copy i, a, b]` with connectors
`[p,x,q]`, keeping all three labels distinct and `p ≠ q`. Assume the hub meets
p and q, a meets p, b meets q, and x lies in both a and b. A supreme occurrence
at a or b would have to replace the hub between two distinct wagon connectors,
contradicting `piece_two_wagon_forces_eq`. Hence the hub supplies both mixed
bridges. The A1--A3 and order arguments are unchanged, and no initial
`WagonVertex p x` or `WagonVertex q x` premise is needed.

For the actual application, the off-core endpoint supplies the hub standard
i. Classify both witnesses at the core endpoint using the actual physical
edge cover. A standard source becomes its prescribed witness-copy label;
active coverage supplies genuine vertex membership. A core source becomes
its genuine physical edge label. Resolve label collisions before constructing
the generalized three-cycle:

| Core-endpoint source labels | Proposed reduction |
|---|---|
| Both equal the hub standard | Existing same-standard block uniqueness. |
| Exactly one equals the hub | The order-one bridge puts the other wagon's shared edge through the vertex in the hub; then use same-standard uniqueness. |
| Both equal another standard | Existing crossing-wagon uniqueness. |
| Both equal one core edge | Their original output parents are already equal. |
| Two distinct non-hub labels | The generalized three-cycle supplies both hub bridges. |

This extension has been checked mathematically but is **not yet a Lean export**
in this contribution. Every core ancestor must retain its equation with the
original output parent. The core/core case remains separate because it lacks
the common standard owner furnished by an off-core endpoint.

The remaining three- and four-segment configurations still require an
argument. Replacement edges must preserve
the original generated wagon labels and actual physical incidences while
reducing the segment count. For the output-strongness auxiliary cycle, only the
unconditional legal reduct and order bounds are available until acceptability
has independently been proved. Global output-wagon strongness, global output
linearity, and the final circulation theorem remain separate obligations.

## Integration

Each new module has a dedicated `Check*.lean` file printing both its elaborated
export signatures and theorem axioms. A separate, focused
`track-b-wagon-geometry.yml` workflow builds all Track B modules from fresh
project objects, audits all their exports and runs both new diagnostics plus
the four existing finite regressions. It checks the actual PR head and does
not alter the shared `lean.yml` workflow or root imports.

The integration lane should also include these modules and Check files in
its complete build and axiom audit. The baseline shared workflow has fixed
lists and does not automatically discover these additions; its green status
alone is not evidence that the new exports were checked. Audit PR #665 proposes
discovery of every module and every Check file, but this Track B work does not
depend on that PR being merged.

No manuscript marker should be promoted for global output strongness or
linearity on the strength of these localized statements.
