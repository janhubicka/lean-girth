# Combined decorated-star realization

The additive `Girth/ACopyDecoratedStar.lean` combines three existing interfaces:
`ACopyExactStar.SourceStar` for points, `ACopyLayeredStar` for actual node and
wagon quotients, and `ACopyPointStar.DiagramEmbedding` for exact overlap-graph
embeddings of the original sources. No prior source file was edited.

## Input and source normalization

`ACopyDecoratedStar.Data` fixes a layered diagram on core/source/shared node
sets, arbitrary core/source/shared point presentations, and source point
setoids. Node-coordinate maps into these presentations are injective modulo
the point setoids. Literal shared-node coordinates have matching shared point
representatives. The maps on the *whole shared point presentation* preserve
and reflect point equality. Thus the shared point presentation can retain the
full induced gluing domain, including chart records outside node support.

Every source point is retained by `coreRecord` or `sourceRecord`. A record
can coincide with an existing node coordinate, and no disjointness or
freshness of records is assumed. The maps `coreMap` and `sourceMap` factor
through the original point setoids; `coreMap_mk` and `sourceMap_mk` are the
factorization equations. Both quotient maps are injective. Exact record
equality and full source intersection theorems follow from the generated
relations, rather than being assumed for the output.

For the streamlined prose, take the point presentations to be the already
realized sets V(H), V(S_i), V(Q_i), with equality setoids. Then these are exactly
the ordinary point pushout maps. There is no requirement that every source
point lie in a node. This specialization retains all chart-point records
without additional occurrence bookkeeping in the recursive proof.

## Derived output

Coordinates descend through the actual level-zero shared-node quotient;
`nodePoint_injective` proves each resulting node chart injective. Core and
source overlap graphs embed exactly via the existing diagram-embedding API.
The coherent overlap realization embeds into the full point quotient and
its image is exactly the union of node-coordinate images. It need not cover
all retained records.

`wagonCarrier` is defined from actual descendant nodes and their coordinate
images. The main carrier results, in `ACopyDecoratedStar.Data`, are:

- `core_wagonCarrier`: core class carrier equals its original embedded carrier
  union every embedded source class which has that exact core contact;
- `private_wagonCarrier`: a noncontacting source class has precisely its own
  embedded source carrier;
- `wagonCarrier_mono`: the generated parent map increases these carriers.

These are derived from the actual node/wagon quotient. They do not assume a
carrier/quotient correspondence. A private wagon label can still share a
point with a core wagon: privacy is a property of node-class contact.

## Regressions and validation

Seven regression declarations check:

1. the source's second node has a genuinely private class;
2. its private wagon carrier still meets the core at a shared vertex;
3. a retained point record can already be a supported coordinate;
4. a retained core point has no supporting node;
5. the supported overlap realization consequently need not be surjective;
6. the private child obtains a core parent and its carrier is retained;
7. an empty source system has an uninhabited top quotient, so vacuous
   universality cannot supply inhabitation.

The exact module build and all seven regressions passed. The strict axiom
checker audits 31 declarations (24 API facts/definitions and 7 regressions);
only `propext`, `Classical.choice`, and `Quot.sound` occur. Neither new source
has warnings. Source hashes and theorem names are in
`decorated-validation.json`. Earlier dependency warnings and the local
Batteries compatibility warning remain visible in the logs.

Reproduction, after sourcing `../runtime/env.sh`:

```
../runtime/with-lean-slot.sh lake build Girth.ACopyDecoratedStar
../runtime/with-lean-slot.sh lake env lean CheckACopyDecoratedStar.lean
python3 scripts/check_axioms.py \
  checks/a-copy-combined-20261109/decorated-axioms.log \
  CheckACopyDecoratedStar.lean
```

## Frontier

This interface does not force output linearity, injectivity of the map from
nodes to carrier *sets*, induced relational source embeddings, or completeness
of the specified nodes among all relational A-copies. Full induced node-domain
exhaustiveness and the relational support/bridge hypotheses remain additional
geometric obligations. A separate full-domain module is being built on this
validated interface. No claim of whole-recursion validation is made here.
