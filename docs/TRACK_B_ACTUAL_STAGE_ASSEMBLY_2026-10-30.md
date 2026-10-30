# Track B: literal next stages and untouched active support

Starting point: main `38abd9a031d87102b3153d4ea0b9d41e0533543f`, including
Track B PR #701 and the independent Track D PR #695.
Scope: the circulation proof; no appendix changes.

The previous pass established genuine selected-label equivalence, bottom
forest invariants, and identity dispatch for trivial physical fibres. This
pass connects those results to the actual recursive transition and makes
the complete untouched support available to the refinement argument.

## The actual standard embedding is the transition map

`TrainSelectedPictureTransition` identifies the physical A-edge of a
composed standard embedding with the canonical physical standard edge.
Generated-train restriction then proves preservation and reflection at
every cut. Only interior compatibility is supplied: the bottom equality
and universal top follow from the injective shared-edge maps.

Selected copies transport with their literal prescribed base labels.
There is no quotient by equal carriers and no need for physical selected
injectivity in this transport theorem. A local Ramsey family selects a
homogeneous standard with both the selected-label and train clauses.
The ordinary family arrow on all relational A-embeddings also supplies
the required projected-colouring form by extending the colouring outside
the active projection, when the colour type is nonempty.

These transition facts require no output linearity, girth, strongness,
finiteness, or assumed completed stage.

## Complete physical support of an untouched fibre

`TrainUntouchedActiveDecomposition` concerns every physical A-edge
contained in the true active carrier. For finite ordered A and an honest
partite projection, every such edge has the prescribed projection.

Let alpha and beta be distinct base embeddings, with alpha processed and
beta untouched. If every core vertex has a part in alpha's carrier, a
beta-projected A-copy cannot lie wholly in the core. Finite equal-size
base carriers and ordered rigidity give a private part. This argument
also handles one-vertex A; no independent two-vertex assumption is added.

Irreducible localization gives a standard owner for each new untouched
edge. A private vertex identifies its standard index, and injectivity
of that standard identifies its entire old edge. Consequently the map

`I × OldActivePhysicalSupport ≃ NewActivePhysicalSupport`

is a genuine equivalence. Its carrier is the full standard image, and
the generated train restricts exactly on each standard. No actual edge
is deleted or replaced by a chosen projected representative.

Different standard active carriers may intersect, but only over the
intersection of the two physical base copies. Base A-linearity makes
that set of parts a subsingleton. This is a bound on base parts, not a
claim of disjoint vertex carriers.

## The new child-girth mechanism retains labels

`TrainUntouchedChildGirth` proves the labelled girth bound for a child
carrier family with an injective child-to-standard owner map, each child
contained in its owner's true untouched active subsystem.

An alleged cycle of length at most g uses at most g distinct standard
indices. Its physical connectors between standards lie in the core
images and over the intersection of the two base copies. That intersection
is at most one part. Actual irreducible A-edges meet its inverse image
in at most one vertex, so the corresponding local gluing forest restricted
to this part has an acyclic labelled incidence graph. The original distinct
cycle connectors contradict that acyclicity.

Only the used gluing family must be a forest. The actual finite-set mixed
forest invariant supplies this through its local-family bridge when the
physical gluing pieces are injective. No full-family forest, output girth,
core-support restriction, or deduplication of equal child carriers is
assumed. The owner injection and child containment are explicit inputs;
connecting them to the appended refinement's complete quotient-labelled
child family remains part of the refinement assembly.

## The complete next stage is assembled from local data

`TrainSelectedPictureStageAssembly` records genuine local inputs in
`ActiveAttachmentBounds`, then constructs the literal attached
`ForestTailStage` and its selected `PictureStep`.

The inputs retain core partiteness, irreducible-to-A coverage, the fixed
target's two distinct physical edges, selected base strongness, interior
shared-train compatibility, the local bottom forest/girth alternatives,
core adjacent parameters and intrinsic full system girth above two at
interior cuts. The indexed output supreme-cycle conditions are explicitly
supplied: these are the remaining positive-cut transfer obligation, and
naming the field does not prove that transfer. Output pretrain linearity
is derived from intrinsic geometry. The order-one bounds needed for
parameters follow from the core full bounds.

The constructor derives:

- finiteness and partiteness of the actual free attachment;
- physical A-linearity from the proved output bottom girth;
- a genuine ambient A-edge and support coverage of every output vertex;
- literal transported selected copies, their physical injectivity,
  selected-or-A irreducible coverage and strongness;
- exact target-train restriction through each selected standard;
- every adjacent allowed-part parameter, using intrinsic core inputs;
- the complete bottom mixed forest;
- actual-selected tail system girth by the genuine label equivalence.

Core irreducible coverage applied to the empty irreducible already
supplies an ambient A-edge. Thus the stage constructor does not require
an inhabited gluing-index type. The local Ramsey arrow itself selects
an actual standard when a `PictureStep` is needed.

No complete next stage, output pretrain linearity, output support coverage,
output selected injectivity, output train restriction or output parameter
bound is assumed. The construction retains every ambient physical A-edge.

## Remaining boundary and validation

Actual nontrivial local witness existence, the indexed positive-cut supreme-cycle
bound, and preservation of the remaining-fibre refinement invariant are
still construction obligations. The support decomposition supplies the
physical input to refinement transport, and the child-girth mechanism is
proved for families with injective standard owners. The appended partition,
its parent and owner maps, preservation of the earlier refinement cuts,
and allowed-parameter localization are not assembled here. No unconditional
forest Ramsey theorem is claimed.

Every exported definition and theorem has an explicit `#print axioms`
check. The focused Track B workflow builds the added modules from fresh
project proof objects, audits all listed exports, runs its finite geometry
and boundary regressions, and retains the logs. Complete exact-head focused
and repository-wide CI, including post-job steps, are required before
merge and before the manuscript's proof links are marked verified.
