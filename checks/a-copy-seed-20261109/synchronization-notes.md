# Seed colour synchronization

The new `Girth/ACopySeedSynchronization.lean` is an additive module. It works
with physical-node sets and indexed designated families, independently of
relational realizations. The six exported theorems are:

- `familyArrow_of_synchronizes`: one colouring of the base, realized by a
  designated lift of each base member, transfers the base Ramsey arrow.
- `factor_through_of_fibreConstant`: colours constant on projection fibres
  extend to a colouring of the entire seed. Empty fibres receive an arbitrary
  colour; only nonemptiness of the colour type is required.
- `backwardFusion`: a finite sequence of fibre-homogenizing steps produces a
  single admissible initial-to-final embedding, constant on each processed fibre.
- `factorization_of_finitePass`: if the profile list covers every nonempty
  initial fibre, the selected colouring factors through the seed projection.
- `synchronizes_of_factorizingSelections`: exact transport of the initial
  designated charts converts such a selection into the synchronization property.
- `synchronizes_of_finitePass`: combines the preceding construction and chart
  transport into the synchronization interface used by the proposed seed theorem.

All names are in `StructuralRamsey.Girth.ACopySeedSynchronization`.

## Exact scope

The finite pass uses an explicit predicate `Allowed i j f` on node embeddings.
It assumes closure under identity and composition. Each local step returns an
allowed projection-preserving embedding, homogeneous on the processed fibre.
The chart-transport hypothesis is required for allowed initial-to-final maps.
Thus the proof does not silently turn arbitrary projection-preserving node maps
into embeddings of designated decorated diagrams.

No theorem here supplies those local steps, proves their geometric invariants,
constructs a train refinement, or proves faithful realization. Those remain
separate geometric/recursive obligations. `Projects` only asks that every node
of a lifted chart projects into its named base chart; this is the exact amount
needed by the colour-transfer conclusion. Geometric applications provide more.

The profile list need not be repetition-free for backward colour selection.
The separate geometric refinement construction can still require freshness.
Neither finite colours nor a finite seed are needed by these conditional
colour arguments; a finite list covering nonempty initial fibres is explicit.

## Finite negative regression

The base has three nodes, with all three two-element subsets as designated
members. Every two-colouring has a monochromatic designated member. The lift
is three disjoint pairs, one for each base member. Its chart projections are
injective and have exactly the named base images; all base members lift and all
lifted nodes are covered. Colour each pair by its second Boolean coordinate.
Every lifted member is bichromatic. Thus exact chart lifting is insufficient
for the Ramsey conclusion, and the synchronization predicate is false.

This regression is at the node-family level. It does not claim a formalized
geometric covering theorem or a decorated relational realization. A separate
regression checks the extension across an empty seed fibre.

## Reproduction

Source `/workspace/scratch/095f642caf71/runtime/env.sh`, then run through
`/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh`:

```
lake build Girth.ACopySeedSynchronization
lake env lean CheckACopySeedSynchronization.lean
python3 scripts/check_axioms.py \
  checks/a-copy-seed-20261109/synchronization-axioms.log \
  CheckACopySeedSynchronization.lean
```

The fixed runtime uses Lean 4.35.0-rc3 and the restored Mathlib cache. The
pre-existing warning about the local Batteries compatibility adjustment is
unrelated to these sources. No whole-repository rebuild is claimed.
