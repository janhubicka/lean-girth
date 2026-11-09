# A-copy applications and singleton-first-cut simplification

Continuation of `validation/a-copy-foundations-20261109`, based on
`191ac8a6d5fc99b7cf314ea1df7d8451949f666a`. Only new source/check/log files
are added. No existing APIs, workflow files, dependency sources, or ongoing
validation checkout were changed.

| Modules | Strictly audited declarations | Scope |
| --- | ---: | --- |
| `ACopyPointStar` | 38 | Coherent supported-point gluing, exact source intersections, output point realization; includes a full-domain counterexample. |
| `ACopyLayeredStar` | 50 | Generated nested equivalences on the actual node pushout, exact restrictions, quotient parent commutation, upward contacts, and universal top. |
| `TrainSingletonFirstCut`, `TrainSingletonFineWitnessBounds` | 5 | First-child acyclicity from transversality, refinement reconstruction without bottom girth, and actual global gain with the retained-cut bound. |

All four new modules and their check files compile with local Lean 4.35.0-rc3.
The 93 transitive axiom checks allow only `propext`, `Classical.choice`, and
`Quot.sound`. No new axiom or `sorry` occurs. These are targeted local checks,
not a claim of a fresh whole-repository build or completed recursion.

The point and wagon applications deliberately do not assert a combined
decorated realization. Unsupported chart points, exact physical support, and
the point/node/wagon carrier compatibility still need their own bridge.
The finite point-star regression explains why the link must contain all
physical nodes on its point domain. Mere coherent overlap embeddings do not
ensure this. The manuscript already requires induced full link domains.

The singleton simplification is local to reconstructing the returned refinement.
It does not remove mixed forests from the outer forest increment, nor the
retained cut needed for global localization. The empty-tail universal-top
specialization remains separate from the new retained-cut wrapper.

Each paired note records exact exports, assumptions, commands and limitations.
The repository's existing CI discovers all new module/check files automatically.
