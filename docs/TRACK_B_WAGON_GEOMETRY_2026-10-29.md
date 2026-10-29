# Track B: localized output-wagon geometry

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

## Remaining Track B obligation

These results cover blocks whose **two endpoint witnesses lie in one source
piece**, for all three combinations: standard/standard, core/core and
standard/core. An arbitrary generated wagon can have its two endpoint witnesses
in different pieces. The new results do not assert that such a block has already
been localized.

The next proposed interface is cross-standard wagon uniqueness: for distinct
standards i,j, at most one generated output wagon contains a physical edge
from each of i and j. The existing cross-standard shared-edge incidence
theorem identifies each candidate with the image of a core wagon;
`no_two_designated_meet_two_wagons` then excludes two candidates. This reduction
uses the core order-two local-piece bound and exact shared compatibility,
without old linearity or strongness. Together with same-standard comparison
and actual off-core edge ownership, it should give global wagon-pair uniqueness
when both common vertices are outside the core. This is a mathematically
reviewed next step, not a new Lean export in this change.

Cases with a common core vertex and the remaining three- and four-segment
configurations still require an argument. Replacement edges must preserve
the original generated wagon labels and actual physical incidences while
reducing the segment count. For the output-strongness auxiliary cycle, only the
unconditional legal reduct and order bounds are available until acceptability
has independently been proved. Global output-wagon strongness, global output
linearity, and the final circulation theorem remain separate obligations.

## Integration

Each new module has a dedicated `Check*.lean` file printing both its elaborated
export signatures and theorem axioms. A separate, focused
`track-b-wagon-geometry.yml` workflow builds these three modules from fresh
project objects, audits all their exports and runs the new diagnostic plus
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
