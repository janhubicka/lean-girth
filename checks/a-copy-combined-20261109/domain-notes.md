# Full induced node domains

`Girth/ACopyFullDomain.lean` derives output physical-node carrier injectivity
from the combined decorated-star construction. Its hypotheses are entirely
source-local:

- The core node carriers in the core's original point quotient are injective.
- Each standard's node carriers in its original point quotient are injective.
- Whenever a standard node's complete carrier lies in that standard's shared
  point domain, the node is in the shared node domain.

The last condition is `FullNodeDomains`. It is not mere coverage of shared
points by some shared nodes. A source node contained in the output core has
all its point classes in the original shared point domain by exact point
intersection. Fullness makes it a shared node. Equal-carrier nodes from
different sources therefore reduce to the core, where the original carrier
map is injective. Same-source equality uses injectivity of the original point
map and native carrier map. Output linearity and actual-copy completeness are
not premises. No nonempty or nontrivial coordinate-set hypothesis is needed.

The two carrier-reflection lemmas reuse `Set.range_comp'` and
`Set.image_injective`, rather than repeating pointwise image proofs.

The regression is the three-edge path on four vertices. Two copies share the
outer edges, covering every point, but their middle nodes remain distinct
with equal generated point carriers. Both local carrier maps are injective,
and the path is linear. Thus active point coverage does not replace full
induced node domains. Sharing every node repairs the omitted condition, and
the positive regression invokes `nodeCarrier_injective`.

The target build and strict axiom audit passed for all 19 declarations: eight
general lemmas and eleven regression/helper declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. There are no warnings in the two new
sources. The existing Batteries compatibility and dependency warnings remain
recorded in the build log. Exact hashes and declarations are in
`domain-validation.json`.

After sourcing `../runtime/env.sh`, reproduce with:

```
../runtime/with-lean-slot.sh lake build Girth.ACopyFullDomain
../runtime/with-lean-slot.sh lake env lean CheckACopyFullDomain.lean
python3 scripts/check_axioms.py \
  checks/a-copy-combined-20261109/domain-axioms.log \
  CheckACopyFullDomain.lean
```

This bridges node-carrier uniqueness. Relational reconstruction, coincidence
of the generated model with the genuine attachment, and the recursive
witness construction remain separate. The generic chart-coverage theorem
supplies actual-copy exhaustion once its honest chart embeddings and coverage
have been established; this file does not assume those conclusions.
