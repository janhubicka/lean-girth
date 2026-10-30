# Track B: intrinsic and recursive-stage geometry

Original geometry base: `7813765c03d2709ab3941d6ab02383e25688e438`.
Integrated publication base: `d5257e9326f70804adf6f12e8f09702aacf24b6c`,
including the subsequently merged Track A positive-cut/source-linearity
interfaces and Track D two-cut and short-triangle results. Their sources
are retained unchanged.
Scope: the circulation manuscript; the appendix is unchanged.

PRs #675, #677 and #679 established complete generated-wagon strongness and
linearity from explicit source geometry. This continuation connects those
results to the intrinsic local witness and the actual recursive old stage.
It does not assert the existence of the required local Ramsey witness or
the full circulation theorem.

## The representation gap

The old geometry theorem reads core incidence on the embedded core vertices
inside the attachment. The inductive witness is supplied on its own vertex
type. The earlier parameter bridge transported only the order-one condition.

`TrainVertexImageSystemGirth` proves full system-girth transport under an
injective vertex image. Physical edges, designated labels, copy-edge sets
and wagon parents remain literal. Every vertex connector of an image cycle
has a preimage because of its left incidence; wagon connectors already have
the same labels. Pullback preserves A1, A2, A3 and twice-order exactly.
The previously checked literal physical map transports the entire supreme
plan and its genuine resulting BigCycle. Thus the global replacement
obligation is preserved, rather than discarded in favor of local pieces.

No nonempty vertex type, finite support or coverage of unused vertices is
assumed. This is transport along one injective representation, not a theorem
about contracting or combining several attached standards.

## Literal local-witness data

`TrainActiveGluingWitness` identifies the shared-support representation with
the whole prescribed core gluing images:

- The union of the image shared-edge carriers is exactly the image of the
  true active subsystem. This uses active support coverage.
- The image shared-edge labels are exactly the actual core A-support edges
  contained in that prescribed image. Embedding reflection gives the
  reverse inclusion.
- The entire OrderOneData records agree, retaining each prescribed label,
  every ambient core edge and its original quotient parent.

`TrainFullGirthCopyStrongness` removes a further redundant premise. A full
local system-girth bound at a cutoff at least two forces every complete
gluing image to be A-strong. The acceptable two-vertex cycle consisting of
that designated copy and an ambient pair edge has a designated supreme
occurrence. Its replacement cannot be long, because the ambient pair edge
is present. A short replacement supplies a copy-owned edge through the same
distinct pair; physical edge linearity identifies it with the original edge.
Whole-edge ownership in the literal witness gives complete containment.

This uses whole-image incidence and actual ambient edges. Strongness of
constituent selected subcopies is never substituted for whole-image
strongness.

## Endpoints do not need cycle bounds

`TrainEndpointGeometry` separates the bottom and universal top from the
strictly interior train cuts.

| Cut | Complete wagon carrier | Source of linearity and strongness |
|---|---|---|
| Bottom, 0 | One physical A-support edge | Ambient A-linearity |
| Interior, 0 < μ < m | The generated quotient wagon | Old wagon linearity and intrinsic core system girth at a cutoff at least 2 |
| Top, m | The union of all actual A-support edges | Physical edge linearity; the top support contains every ambient A-copy |

The top support need not contain every ambient vertex. Empty supports and
height zero are covered by the same theorems. No extra top system-girth
coordinate is added.

## Discharged and retained hypotheses

`TrainSelectedPictureIntrinsicGeometry` supplies the geometric conclusions
at one cut and at all cuts. `TrainSelectedPictureStageGeometry` consumes
the existing `ForestTailStage` fields directly.

| Input to the previous geometry theorem | Source in the new interface |
|---|---|
| Strongness of the true active subsystem | Partiteness over an A-linear base and rigidity of the chosen base A-copy |
| Nonempty shared support for every attached standard | A genuine projected A-copy in the active fibre |
| Shared-train compatibility at every level | Compatibility only at interior cuts; equality and universality handle the endpoints |
| Core-image LinearPretrain and local order-two bound | Full intrinsic local-witness system girth, transported with the same cutoff |
| Whole attached-standard strongness | Active strongness plus whole gluing-image strongness, the latter derived from an interior local full bound at least two |
| Old physical A-linearity | The old stage's `aLinear` field |
| Old interior wagon linearity | The old stage's `tailGirth` field |
| Bottom/top output geometry | The endpoint lemmas above |

The resulting output has relational A-linearity, LinearPretrain at every
train cut, and AStrong for every complete generated wagon. No output
linearity, output strongness or output cycle-transfer conclusion is an input.

For height at least two, the stronger interfaces use the genuine interior
cut 1 to derive old/core physical A-linearity as well as whole gluing-image
strongness. These three hypotheses are absent from their stored types. The
remaining local-witness assumptions are exact interior train compatibility
and full intrinsic witness system girth at interior cutoffs at least two.
The recursive-stage interface obtains the old interior linearity from its
existing tail-girth field. Its base A-linearity, rigidity, irreducibility and
actual active projected copy remain explicit.

For the general interface, including heights zero and one, source physical
A-linearity and whole gluing-image strongness remain explicit because there
may be no interior cut from which to derive them. No spurious endpoint
cycle bound is introduced to hide that case. An absent
projected fibre is handled by the already existing identity-step interface;
the new active theorem does not postulate a copy in an empty fibre.

## Verification and remaining integration

Every public definition and theorem in the six new modules has a matching
explicit `#print axioms` check. The focused Track B workflow builds and
audits all six modules as well as the existing geometry suite. The full
repository workflow discovers every proof module and Check file from the
checkout, runs the audit-tool tests and the finite regressions. Complete
exact-head success is required before merge.

The companion TeX revision states the all-level geometry result, explains
the endpoint cases and intrinsic image transport, and narrows the remaining
source-hypothesis marker. It preserves compact colored clickable annotations.
Its local compile and visual review follow the user's standing exception for
the unavailable TeX Actions quota.

Still separate are construction of the required local witness, positive-cut
global cycle transfer, assembly of the next stage's full system-girth and
forest invariants, and the final recursive witness-existence theorem.
This continuation discharges geometric interfaces, not those conclusions.
