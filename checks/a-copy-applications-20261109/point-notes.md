# Supported point-star application — local validation

Date: 2026-11-09. Published foundation base:
`191ac8a6d5fc99b7cf314ea1df7d8451949f666a`.

## Result and exact input

New standalone module: `Girth/ACopyPointStar.lean`.
New audit/regression module: `CheckACopyPointStar.lean`.

The module instantiates the existing `ACopyExactStar.SourceStar` theorem with
actual coherent-diagram point occurrences `Ω × K`, as in the point row of
`paper/11-amalgamation.tex`. It uses the supported point realization from
`paper/03-partite-construction.tex`. It is independent of the wagon application.

`ACopyPointStar.DiagramEmbedding` consists of an injective map on node labels
that preserves and reflects the complete binary coordinate overlap graph.
`ACopyPointStar.Data` supplies core, source, and shared coherent diagrams and
such embeddings from every shared diagram into its core and source.

`occurrence_compatible` is derived by composing the two overlap equivalences.
The output `Point` is literally `Quot Step`, with `Step` the existing
`SourceStar.Step`: source overlap equalities and literal shared-coordinate
identifications. No output injectivity, no exact intersection, no normal form,
and no final quotient equality criterion is assumed.

## Main exports

All names below are under `StructuralRamsey.Girth.ACopyPointStar.Data`.

| Exports | Checked conclusion |
| --- | --- |
| `coreOccurrence_injective`, `sourceOccurrence_injective` | The literal occurrence maps induced by the shared node embeddings are injective |
| `occurrence_compatible` | Shared overlap preservation/reflection supplies the generic exact-star hypothesis |
| `coreMap`, `sourceMap`, their `_nodePoint` and `_injective` theorems | The original core and source point quotients embed in the generated point quotient |
| `corePoint_eq_iff`, `sourcePoint_eq_iff` | Generated equality restricts exactly to the original overlap graphs |
| `sourcePoint_eq_corePoint_iff` | Source/core equality has an explicit shared node and coordinate witness |
| `sharedPoint_eq` | Every literal shared-coordinate identification holds |
| `distinct_sourcePoint_eq_iff_core` | Equality across distinct sources passes through an actual core occurrence |
| `distinct_sourcePoint_eq_iff` | Cross-source equality is exactly source overlap to a shared coordinate, core overlap between the shared coordinates, and overlap into the other source |
| `coreImage_eq_range_coreMap`, `sourceImage_eq_range_sourceMap` | The occurrence-image sets are exactly the images of the quotient point maps |
| `sourcePoint_mem_coreImage_iff` | Contact holds exactly when the entire source point class meets a shared node occurrence |
| `sourceImage_inter_coreImage` | Source/core intersection equals the shared-node point image |
| `distinct_sourceImage_inter` | Distinct-source intersection equals the intersection of their shared images in the core |
| `point_covered`, `nodePoint_covered` | Every output point is represented by a physical-node occurrence |
| `nodePoint_injective`, `nodeEmbedding` | No coordinate folds inside any raw output node |
| `output`, `output_rel_core_iff`, `output_rel_source_iff` | Reading point equality gives a coherent complete overlap diagram with exact source restrictions |
| `outputPointEquiv`, `outputPointEquiv_nodePoint` | Realizing that completed diagram yields the same generated point quotient, commuting with every node coordinate |

Auxiliary definitions `Raw`, `Step`, `Generated`, `Point`, `corePoint`,
`sourcePoint`, `coreImage`, `sourceImage`, `sharedImage`, and `Node` expose the
actual carrier types and generating relations.

## Regressions

`ACopyPointStarRegression` uses two-point charts with a cross-coordinate
intersection and checks:

- A nonshared source-node occurrence reaches a different source through
  shared representatives and the core overlap, both as quotient equality and
  as the actual generated relation.
- Distinct original points do not fold in core or source.
- A source class with no shared representative remains off the core, and
  private points from different sources remain different.
- Linear source diagrams can produce distinct raw shared-node labels with
  equal full carriers; the raw-node output diagram is then not linear.

`ACopyPointStarFullDomainRegression` formalizes a stronger boundary example.
Both core and source have the linear edge family `xy`, `xu`, `vy`, but only
`xu` and `vy` are declared shared. Both endpoints of `xy` glue, and its two
copies have equal output point carriers. Nevertheless, the equivalence
generated on node labels by only the shared-node identifications keeps those
two `xy` labels distinct. The checks are `diagrams_linear`,
`missing_edge_coordinates_glue`, `missing_edge_carriers_equal`, and
`missing_edge_nodes_separate`.

This is not a counterexample to the manuscript: the chosen shared point
domain is not induced/full because it omits the edge `xy` on its points.
It demonstrates why a correct point quotient plus shared-node identification
does not alone prove physical-node exactness.

## Validation

Lean 4.35.0-rc3, using the existing isolated dependencies. Each Lean command
ran after sourcing `/workspace/scratch/095f642caf71/runtime/env.sh`, through
the shared two-slot wrapper `runtime/with-lean-slot.sh`:

```sh
lake env lean -DwarningAsError=true Girth/ACopyPointStar.lean \
  -o .lake/build/lib/lean/Girth/ACopyPointStar.olean
lake env lean -DwarningAsError=true CheckACopyPointStar.lean
python3 scripts/check_axioms.py \
  checks/a-copy-applications-20261109/point-axioms.log CheckACopyPointStar.lean
```

All commands exited zero. The strict checker reports **38 declarations**:
24 application declarations and 14 regression declarations. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. There are no new axiom declarations
or proof placeholders. The known preexisting Lake batteries working-tree
warning comes from the runtime compatibility patch; Lean source warnings are
treated as errors.

Logs: `point-compile.log`, `point-axioms.log`, `point-strict-axioms.log`.
No existing modules, root imports, lake files, runtime/dependencies, manuscript
files, or Git state were edited. No package update or global rebuild occurred.

## Actual simplification and remaining obligations

There is no second path-normal-form argument: the source/core, source/source,
and injectivity results directly reuse `SourceStar`. Completing and realizing
the overlap diagram reuses `CoherentOverlap.ambientEquiv`. The only
application-specific input proof is overlap compatibility on shared
coordinates; remaining proofs translate that generic result into diagram
and carrier language.

All source points in this construction are supported occurrences. To cover a
decorated relational realization, one must additionally include retained
chart-point occurrences and prove that the prescribed active gluing domain
is exactly covered by the shared physical nodes. An extra chart occurrence
can be equal to a supported occurrence: its syntactic extra tag does not
make its point class private. Privacy concerns a whole class having no shared
representative.

Full induced relation/order/part reconstruction and exact actual A-copy
coverage remain unproved here. `output` intentionally uses the disjoint sum
of raw node labels. A basic-node pushout and its correspondence with actual
physical copies require further geometry, including the full/induced gluing
domain condition highlighted by the regression. No linearity, strongness,
train parameter, wagon, or cycle conclusion follows from this module alone.
