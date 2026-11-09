# Singleton first-cut simplification

The new `TrainSingletonFirstCut` module proves four declarations. A labelled
family with transversal edges and intersections in one permitted part has no
Berge cycle. The fibre version applies to the complete child family of one
parent, preserving every quotient label. Two constructors fill the existing
`FirstWagonRefinement` record from this zero-child fact and the strictly positive
child/system bounds. No bottom girth or forest premise is used.

`TrainSingletonFineWitnessBounds` proves one additional declaration:
`selectedPicture_actualSupport_girthGain_of_singletonSystemCuts`. Compared with
the existing actual-support girth theorem it omits precisely `hBottom`.
Transversality comes from irreducibility and the actual partite system.
The retained first-cut full-system bound remains explicit. This additive global
wrapper certifies the retained-cut route; it does not replace the separate
universal-top argument for an empty tail. The new refinement constructors also
apply to that argument with the existing universal-first-wagon gain theorem.

This is a local dependency simplification. Mixed forests through q−1 are still
required by the outer forest increment. The singleton parameter gives acyclicity
inside each first fine wagon, not global equality-cut girth by itself.
The old refinement definition, every old API, and existing source files are
unchanged. Independent source review is recorded in the manuscript's
`internal/a-copy-applications-20261109/simplification-referee.md`.

## Local checks

Lean 4.35.0-rc3, the repository's pinned Mathlib revision, private dependency
cache, `runtime/env.sh` and `runtime/with-lean-slot.sh`. The two new modules and
the two corresponding check files compile with `-DwarningAsError=true`.
`scripts/check_axioms.py` passes all five declarations, allowing only
`propext`, `Classical.choice`, and `Quot.sound`.

Three previously uncached legacy modules in the dependency chain were compiled
without changing their sources. They emit pre-existing style/deprecation
warnings, recorded in the logs. This does not weaken the strict transitive
axiom audit. There are no new axioms or `sorry` declarations.

Commands (after sourcing the runtime and using its two-slot wrapper):

```sh
lake env lean -DwarningAsError=true Girth/TrainSingletonFirstCut.lean -o .lake/build/lib/lean/Girth/TrainSingletonFirstCut.olean
lake env lean -DwarningAsError=true Girth/TrainSingletonFineWitnessBounds.lean -o .lake/build/lib/lean/Girth/TrainSingletonFineWitnessBounds.olean
lake env lean -DwarningAsError=true CheckTrainSingletonFirstCut.lean
lake env lean -DwarningAsError=true CheckTrainSingletonFineWitnessBounds.lean
python3 scripts/check_axioms.py checks/a-copy-applications-20261109/singleton-axioms.log CheckTrainSingletonFirstCut.lean
python3 scripts/check_axioms.py checks/a-copy-applications-20261109/singleton-fine-axioms.log CheckTrainSingletonFineWitnessBounds.lean
```
