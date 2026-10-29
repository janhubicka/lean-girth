# Track D: initial cuts, refinements, and concrete Ramsey geometry

This continues the checked checkpoint in merged [PR #669](https://github.com/janhubicka/lean-girth/pull/669).
The continuation branch is `circulation-d-initial-refinement-oct29`, based on
merge commit `b9e86cdb75356b68e87af7504b213c90d83850ce`.
Current validation results are recorded in [PR #671](https://github.com/janhubicka/lean-girth/pull/671).
The circulation-only contracts in #663/#664 and the audit #665 still apply.

## Construction obligations discharged

### Initial tail system girth

`initialTrain_fullSystemGirth_of_targetCut` proves the existing
`FullSystemGirthGT q` for the actual selected initial picture at every proper
cut `mu`, from target A-linearity and labelled target wagon-cut girth `>q`,
where `q >= 2`. It assumes neither initial system girth nor a localization
or replacement conclusion.

Every actual initial A-edge has its exact component/target-edge coordinates.
At a proper cut, the wagon labels inject into component/target-wagon pairs,
with exact carrier images. Vertex and wagon incidence preserve components,
so every initial big cycle is contained in one literal component. If a
designated label occurs, it is supreme by the checked identity replacement
plan, whose output is the original genuine cycle.

For an edge-only cycle, the source order supplies the missing quantitative
bound. Universally, twice the number of vertex-connector positions is at
most `C.twiceOrder`. If the parent word is nonconstant, each used parent
has an outgoing change; its connector is a vertex. Thus

```
number of used parent labels <= number of vertex positions <= q.
```

Restricting the labelled cut to these actual parent labels gives an acyclic
incidence graph. Cyclic run compression contradicts a nonconstant parent
word. In the constant-parent case, A1--A3 and physical edge linearity rule
out every acceptable cycle: the no-wagon case reduces to two distinct edges
sharing two vertices, the one-wagon two-occurrence case violates A1 at order
one, and the one-wagon three-occurrence case violates A2 using an actual
ambient pair edge.

Distinct wagon labels are never identified merely because their carriers
coincide. The passage to ordinary girth on the range of carriers is used
only together with the pairwise intersection condition derived from labelled
girth greater than two. Repeated nonadjacent source labels and length two
are included. The universal top cut is not claimed to preserve components.

`initialTail_of_targetCuts` supplies exactly the former `hInitialTail`
argument. It derives target A-linearity from the ordinary head support-girth
bound and takes the natural labelled target cut bound at each positive
coordinate. `initialForestTailStage_of_targetCuts` therefore constructs the
whole finite initial stage from target data alone.

### Initial refinement readiness

For finite, nonempty, irreducible A, every physical A-edge contained in an
initial active carrier is the carrier of an actual projected fibre copy.
This uses component factorization, injectivity of the component projection,
and finite containment between A-copies. It needs no ordered-source
rigidity. The complete active support is consequently a matching; no actual
active edge is omitted.

`FirstWagonRefinement` records the manuscript's finite nested refinement:
positive depth; equality at its bottom; the original first relation at its
last inserted level; preservation and reflection of every higher original
level; allowed-part sets contained in the original first allowed set and
of size at most one; sibling parameters; and labelled girth on all child
classes of each parent.

`firstWagonRefinement_of_matching` constructs this data at every finite
positive depth and every finite girth budget. Inserted equality levels and
empty allowed-part sets satisfy the exact at-most-singleton requirement.
This is a construction on actual relations and all physical edges, rather
than run-count arithmetic applied to an assumed refinement.

`ForestTailStage.FirstRefinementReady` is the corresponding concrete
remaining-profile invariant. Its initial theorem and its `.tail` law
discharge both initial readiness and the empty-profile drop premise.
Preservation through a nontrivial attachment remains separate.

### Output ordinary girth and local strongness

`girthGT_of_finiteMixedForestThrough` proves that a mixed invariant testing
every ambient one-edge piece implies ordinary support girth at the same
cutoff. It applies the existing forest-union girth theorem to the finite
pieces of a purported Berge cycle.

`actualPartiteDesignatedAB_forest_and_girth_of_localGeometry` removes the
previous output-girth input. Before applying the increment, it derives old
A-linearity from the old mixed bound, core A-linearity from core girth,
strongness of the true active source from base A-linearity and profile
rigidity, and output A-linearity from the existing actual attachment
geometry theorem. Ordinary output girth `>2` follows at this stage.

For cutoffs greater than two, the local mixed bound through `m-1` also
supplies strongness of every local image against every ambient A-edge.
Only the cutoff-two local constructor supplies strongness separately.
After the increment, the new theorem returns both the complete mixed
forest through `m` and ordinary output support girth `>m`.

The core hypothesis remains `GirthGT ... m`. It is not derived from a
local mixed forest through `m-1`; the required one-unit gain is still part
of the refinement-forgetting construction.

### Concrete base Ramsey geometry

`baseTwoRamseyFamily_of_monotone_embeddings` and its ordered-source
specialization use the existing closed-target EHN witnesses to construct
one finite structure and an actual selected B-family with:

- The family-restricted Ramsey arrow.
- A-strongness of every selected image.
- Ambient A-linearity and ordinary support girth greater than two.
- The complete mixed forest bound through two, including every ambient
  A-edge.

The B/B case uses controlled intersections of closed target embeddings;
B/A uses strongness; A/A uses A-linearity. The finite-set formulation
handles duplicated physical pieces without assuming label injectivity.

This endpoint retains the selected family, which would be lost by taking
only the ordinary Arrow corollary. Ambient support coverage, prescribed
partite projection, prescribed train parameters, and completion of the
distinguished output order are not asserted by this EHN endpoint.

### Combined finite construction

`constructFromTargetCuts_of_refiningSteps` constructs one actual finite
`ForestTailStage` with `DesignatedArrow`, using the natural target head and
labelled tail-cut bounds, target support and parameter hypotheses, a
prescribed base-family arrow, and actual inhabited-fibre steps preserving
`FirstRefinementReady`.

It derives nonemptiness of the base family from the arrow, constructs the
initial stage, proves its tail bounds and readiness, and uses the proved
empty-profile drop law. The old abstract `Ready`, `hReady`, `hInitialTail`,
and `emptyReady` arguments are absent. Strong selected copies, exact
all-level train preservation/reflection, adjacent parameters, bottom mixed
forest, every tail bound, and the Ramsey arrow belong to the same output.

The remaining local-step hypothesis is restricted to an inhabited fibre
indexed by an actual base embedding and a stage ready on that profile and
the remaining list. It must construct a new stage preserving the remaining
refinements; this geometric constructor is not supplied by the finite-pass
theorem itself.

### Complete one-edge target case

`exists_orderStage_designatedArrow_of_oneEdgeTarget` constructs a finite
`OrderStage` and its selected Ramsey arrow for every admissible vector when
the complete physical A-support of the target has exactly one edge and
covers all target vertices. The source is finite, nonempty, and ordered.

The base is B itself, with the singleton identity family. Every target cut
has at most one wagon label, so all labelled cut bounds and all adjacent
parameters hold, for arbitrary allowed-part sets. The initial construction
then gives every system-girth cut, including the bottom. Ordered-source
rigidity makes all A-embeddings into B equal, so the literal selected target
copy is monochromatic for any colour type. No local Ramsey operator, base
arrow, initial tail bound, or target parameter bound is assumed.

This completes the covered one-physical-edge target case. It is separate
from the multi-edge cutoff-two construction.

## Remaining noncircular construction boundary

| Boundary | Current state |
| --- | --- |
| Initial picture | Finite stage, all initial tail bounds, complete active support, actual refinements and initial readiness are proved from natural target hypotheses. |
| One-edge target | A complete finite order stage and selected arrow are constructed. |
| General cutoff-two base | Selected EHN Ramsey/mixed-two geometry is constructed; the full supported, parameter-compatible partite/train package and output order completion still require assembly. |
| Larger-cutoff local operator | Construct the finite refined recursive witness, forget/collapse refinements, prove core ordinary girth `>m`, and preserve the remaining fibres' concrete refinements. |
| Nonempty-tail cutoff two | Construct uniform first wagons, contraction to the coloured edge type, colour-word selection, filling/scattering, and all tail/parameter preservation. |
| Fixed forest-to-order conversion | The forest-cycle theorem and source-order segment budget are proved; geometric minimum segmentation, mixed-singleton elimination, old-standard supremeness, and legal physical pullback still require A/B/C integration. |
| Universal recursion | The well-founded assembly is checked; instantiate its actual witness families and every geometric operator. No unconditional universal train Ramsey theorem is claimed. |

All constructions retain the selected B-family and every ambient A-edge.
No deletion of uncovered support edges, arbitrary forest-subfamily deletion,
absent supreme label, output-linearity premise hiding its own conclusion,
or local-to-global replacement inference is used.

## Validation and reproduction

The new proof bodies have passed exact-source diagnostics with the pinned
Lean toolchain and their genuine dependencies, including standard-axiom
audits and independent semantic reviews. The merge gate is the original
import build and latest-head CI, recorded in PR #671 rather than frozen in
this mathematical ledger.

The lane-local gate builds every project module, audits the previous D
exports and all new exports, and runs all four existing finite regression
programs:

```sh
bash scripts/check_track_d.sh
```

Shared `Girth.lean`, shared `lean.yml`, and manuscript/appendix sources are
unchanged. Issue #663 remains open for the construction obligations above.
