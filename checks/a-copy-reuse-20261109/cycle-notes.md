# Shared cyclic-owner localization

`Girth/ACopyCycleLocalization.lean` is additive; all previously validated
modules and theorem interfaces are unchanged. All theorem names are under
`StructuralRamsey.Girth.ACopyCycleLocalization`.

The core assumes a cyclic word of length at least two, pairwise distinct
connectors, and incidence **only at changes of owner label**. An acyclic
incidence graph forces the owner word to be constant. The used-range version
requires acyclicity only on labels that occur. Its girth wrapper obtains
acyclicity from labelled girth greater than `g >= 2` and at most `g` used
labels. No finiteness assumption on unused labels or ambient vertices is
needed; distinct labels remain distinct even when their carriers agree.

The physical-cycle specialization supplies incidence from edge containment.
`singleton_refinement_localizes` uses the old transversality/noninjectivity
lemma to save one used label, then invokes the shared core; it does not call
the previous singleton constancy theorem. `retainedCut_localizes` uses actual
quotient wagon labels and carrier containment; it does not call the previous
retained-cut localization theorem. Thus these wrappers are substantive
applications, not direct restatements of imported conclusions.

The four regressions check that private connectors outside all carriers are
allowed, equal carriers with distinct labels still obstruct girth at cutoff
two, forgetting those labels erases that obstruction, and repeated connectors
can traverse a nonconstant word even in an acyclic incidence graph. The last
example verifies that connector injectivity cannot be silently dropped.

Validation on 2026-11-09 passed: module build, all four regressions, and a
strict transitive axiom audit of eight helper/application declarations plus
four regression declarations. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. There are no warnings in the two new sources. Existing
dependency warnings and the local Batteries compatibility warning are retained
in the logs. Exact hashes and checked names are in `cycle-validation.json`.

Reproduce from the Lean checkout after sourcing `../runtime/env.sh`:

```
../runtime/with-lean-slot.sh lake build Girth.ACopyCycleLocalization
../runtime/with-lean-slot.sh lake env lean CheckACopyCycleLocalization.lean
python3 scripts/check_axioms.py \
  checks/a-copy-reuse-20261109/cycle-axioms.log \
  CheckACopyCycleLocalization.lean
```

These results do not prove recursive witness existence, the full diagram
realization assembly, or the remaining cycle-reduction geometry. They validate
one shared localization argument and its two concrete recursive applications.
