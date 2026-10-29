# Track B: generated output-wagon geometry

This work follows the audited Track B contract in issue #661. The first
contribution used common base `3af405cc3a51ca7d3201e221a8a2a56d2e443751` and
merged as PR #668. The one-off-core continuation starts from integrated main
`65a1bab3e2314f22c4921269ca81f019dbf4de26`, preserving the other lanes.
The direct strongness continuation builds on PR #675 at
`5a1b62b8a8344d983a34d19a8378281d4614e3b7`.
Only the circulation argument is addressed; the appendix is excluded.
The user's continuation explicitly also requests fixing, simplifying and
annotating the TeX draft. Those focused changes belong to a companion PR in
`janhubicka/girth`; this Lean PR does not edit root imports or the shared
workflow.

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

## Arbitrary pairs with one off-core endpoint

The next continuation removes the genuine-core-edge premise entirely. Only
one of the two distinct common vertices must lie outside the core; the other
vertex and all four actual support-edge witnesses are unrestricted.

| Module | Interface | Inputs and scope |
|---|---|---|
| `TrainTwoLabelVertexProbe` | `OrderOneData.twoLabelVertexProbe`, its order and acceptability theorems | A genuine three-occurrence cycle with labels `[hub copy i, a, b]` and connectors `[wagon p, vertex x, wagon q]`. All three labels are distinct and `p ≠ q`; the non-hub labels may be copies or edges. The cycle has twice-order four and satisfies A1--A3 without assuming that x lies in either wagon or in the hub. |
| same | `OrderOneData.copy_bridges_of_two_label_vertex_probe` | Under `LocalPieceSystemBound 2`, the hub supplies a bridge through x in each prescribed wagon. A non-hub supreme occurrence would replace the hub between distinct wagon boundaries, contradicting `piece_two_wagon_forces_eq`. |
| `TrainSelectedPictureOneOffCorePairGeometry` | `attachedSelectedPicture_one_offCore_blocks_parent_eq` | Arbitrary actual endpoint blocks have the same generated parent when one endpoint is off-core. Inputs are old `LinearPretrain`, core `LocalPieceSystemBound 2`, exact shared compatibility and the standing active-attachment data. |
| same | `attachedSelectedPicture_one_offCore_wagon_eq_of_common_vertex_pair` | The complete `WagonVertex` formulation, with no selected source representatives. |
| same | `attachedSelectedPicture_one_offCore_wagon_class_eq_of_common_vertex_pair` | The complete generated quotient-carrier formulation. |
| same | `attachedSelectedPicture_wagon_carriers_inter_subsingleton_of_offCore` | Distinct output wagons sharing an off-core vertex have a subsingleton **whole** intersection, including inside the core. This is stronger than merely removing the core from the intersection. |
| same | `attachedSelectedPicture_parent_eq_of_one_offCore_pair` | An arbitrary actual support edge through a distinct pair of vertices of a wagon has that wagon's parent when one endpoint is off-core. No output strongness or output linearity is assumed. |

For the actual proof, the off-core endpoint y supplies a common standard
owner i. If x is also off-core, the earlier theorem applies. Otherwise,
classify each x-edge using exhaustive actual physical edge coverage. An
edge already in standard i provides its required representative directly.
Every other source gives a literal core-witness label F and a core wagon p
with all of the following retained: `F ≠ copy i`, x belongs to F, F and i
meet p, and the canonical core embedding satisfies `κ p = W` for the
original output parent W. For a standard source, membership in the
prescribed witness copy comes from active-support coverage; it is not
inferred from meeting a wagon.

If one x-edge is already in the hub, its vertex incidence and the order-one
bridge move the other parent into that hub. If both sources are outside the
hub and their output parents differ, their core parents differ. Equal
source labels are impossible: equal copy labels violate the two-wagon
obstruction, while equal physical edge labels immediately identify the core
parents. The generalized probe therefore applies to three distinct labels
and gives both required shared edges in the hub. Their physical shared-edge
identities preserve the original output parents. Old wagon linearity then
compares the two blocks entirely inside one standard.

This proof never localizes a lone arbitrary wagon incidence at a core
vertex. The second wagon and common off-core endpoint are essential to the
argument. No core wagon linearity, strongness, finite support or output
`LinearPretrain` premise is introduced.

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
their precise limitation. The new one-off-core theorem uses the additional
order-one and generalized order-two bridge consequences of the actual
witness bound, which that diagnostic does not impose. These examples are
not counterexamples satisfying the full relational attachment and
system-girth hypotheses.

## Full generated-wagon strongness

The formerly proposed direct strongness route is now implemented. It avoids
the general minimum-segment argument and proves parent-preserving absorption
for every actual ambient support edge and every generated output wagon.

| Module | Interface | Inputs and scope |
|---|---|---|
| `TrainPairEdgeWagonProbe` | `OrderOneData.pairEdgeWagonProbe`, its order and acceptability theorems | Labels `[edge g,F,G]`, connectors `[x,p,y]`, all adjacent labels distinct and x distinct from y. The actual pair edge g remains present. Acceptability requires that p does not contain both endpoints. |
| same | `OrderOneData.twoLabel_wagon_bridge_of_pair_edge` | Under `LocalPieceSystemBound 2`, either F is designated and supplies a p-edge through y, or G is designated and supplies a p-edge through x. No source linearity or global replacement legality is assumed. |
| `TrainSelectedPictureWagonStrongness` | `attachedSelectedPicture_parent_eq_of_wagon_pair` | Any actual support edge through two distinct vertices of an arbitrary output wagon has that wagon's original quotient parent, with no localization premise on its endpoint witnesses. |
| same | `attachedSelectedPicture_outside_edge_wagon_inter_subsingleton` | An actual edge whose output parent differs from W meets the complete generated carrier of W in at most one vertex. |
| same | `attachedSelectedPicture_wagon_aStrong` | Every complete generated `wagonClassCarrier` satisfies the existing relational `AStrong` predicate in the full actual attachment. |

The actual strongness exports retain the standing true active-attachment
data, irreducibility, `hShared` and exact all-level `hRel`. Their additional
inputs are old and core-witness `LinearPretrain`, the core witness
`LocalPieceSystemBound 2`, A-strongness of the whole active subsystem, and
A-strongness of every whole attached standard. They assume no generated
output linearity, output system-girth, finite support, missing-incidence
condition or target-wagon strongness. The geometric whole-standard input
can be supplied by the existing attachment theorem from active strongness
and strongness of each complete core gluing image. Strong constituent
designated subcopies do not by themselves prove strongness of that union.

The one-off-core theorem first handles any pair with an off-core endpoint.
For two core endpoints, `attachment_core_aStrong` and
`actualASupport_core_edge_pullback` turn the ambient pair edge g into a
genuine core edge. Classify arbitrary W-edges through x,y by the actual
support cover. If both come from one standard or both are core edges, the
existing source-local pair absorption theorems finish. Otherwise exact
generated incidence gives a core class p with `κ p = W` and genuine witness
labels F,G containing x,y and meeting p. Active coverage supplies the
prescribed standard-copy memberships.

Assume g has another output parent. Its core parent q then differs from p.
**Source-core** wagon linearity excludes both endpoints belonging to p,
because g puts them in q. The cycle `[edge g,F,G]` with connectors `[x,p,y]`
has twice-order four. Its A2 ambient-nonedge clause has impossible premises
because one endpoint is missing from p; the proof never claims that the
actual pair edge g is absent. A3 follows because the two vertex positions
are consecutive cyclically. Its designated supreme occurrence is F or G,
and the mixed replacement gives an actual p-edge through the opposite
endpoint in that same source.

The shared-edge identity preserves `κ p = W` on transport into the original
standard. Both endpoints of W are now represented there, so whole-standard
A-strongness absorbs g and old wagon linearity identifies its parent with W.
Equal standard sources were already handled in the source-local branch;
an equality between g's edge label and a core endpoint label directly
contradicts the supposed different output parents. Designated one-edge
copies remain distinct from actual edge labels despite equal carriers.

Both new modules have been compiled and all seven declarations have been
reviewed at their stored signatures and audited for transitive axioms. Only
`propext`, `Classical.choice` and `Quot.sound` occur. Exact-head repository
CI remains the merge gate, as for every other contribution.

## Remaining Track B obligation

Arbitrary generated wagon pairs are compared whenever one common vertex
lies outside the core. Full pair-edge absorption is now proved under the
explicit source and whole-piece geometric hypotheses above. Consequently,
distinct output wagons sharing two vertices can do so only when both
vertices lie in the core **and no ambient support edge joins the pair**.
This is the remaining global output-linearity case.

Vertex membership in the core still does not put an incident edge in the
core. A private old wagon can touch the active subsystem in one vertex
without a shared edge. Thus unconditional core localization of every
generated-wagon vertex remains an invalid intermediate target. The
remaining three- and four-segment configurations must retain original
quotient labels, actual vertex incidences and legal replacement words.
The core/core case has no off-core vertex furnishing a common standard
owner automatically.

The companion TeX change replaces the old minimum-segment strongness
argument by the direct checked proof. A strongness marker certifies exactly
the conditional geometric statement above; it does not certify the
recursive construction supplying its hypotheses. Global output linearity,
positive-cut cycle transfer, the remaining construction hypotheses and the
full circulation theorem remain open.

## Integration

Each new module has a dedicated `Check*.lean` file printing both its elaborated
export signatures and theorem axioms. A separate, focused
`track-b-wagon-geometry.yml` workflow builds all Track B modules from fresh
project objects, audits all their exports and runs both new diagnostics plus
the four existing finite regressions. It checks the actual PR head and does
not alter the shared `lean.yml` workflow or root imports.

Audit PR #665 is now integrated: the shared workflow discovers and builds
every `Girth/*.lean` module and runs every `Check*.lean` audit exactly once.
The focused workflow additionally enumerates all twelve Track B modules
and their twelve Check files: 42 exports in total (39 theorems and three
cycle constructions). The two continuations beyond PR #668 add sixteen
exports: fourteen theorems and two constructions. Both workflows must pass
on the proposed PR head before merge.

No manuscript marker should be promoted for global output linearity or
the full recursive theorem on the strength of these geometric statements.
