# Circulation validation: current entry points

Baseline: `3af405cc3a51ca7d3201e221a8a2a56d2e443751`, 29 October 2026.
Scope: the circulation manuscript, not the appendix. **The final Ramsey theorem is not yet formalized end to end.** A checked conditional interface is not a checked application of that interface.

The old cumulative ledger is preserved byte-for-byte as [coverage-history-2026-10-29.md](coverage-history-2026-10-29.md). Its historical pending/open notes are not current status. See [the adversarial audit](CIRCULATION_AUDIT_2026-10-29.md) before starting parallel tasks #660–#664.

`Girth/Circulation.lean` collects the useful current interfaces without making a new mathematical assertion. Importing this facade does not certify the final theorem.

| Area | Reuse first | Still required |
|---|---|---|
| Structural Ramsey/active pictures | `ALinearRamsey`, `ActivePictureInvariant`, `ForestStructuralABCompletion` | Assemble actual local-witness existence and all structural invariants; do not replace the intended external Ramsey input by an undocumented axiom. |
| Direct forest increment | `ForestActualDesignatedTrueActiveIncrement`, `ForestActualDesignatedDirectIncrement`, `ForestJoinLift`, `ForestJoinLiftLinear` | Instantiate genuine old/local forest and active-support hypotheses in the recursion. |
| Zero-cut cycle branch | `TrainActualZeroCutGlobalSupreme`, `TrainActualStandardPhysicalMap`, `TrainActualStandardStrongFromBase` | Supply the explicit strongness and train-compatibility hypotheses in the full construction. The conditional zero-cut transfer itself is checked. |
| Positive-cut reduction | `TrainActualPositiveCutSupremeOrBridges`, `TrainActualCutIndexedBigCycle` | Lift the reduced witness's plan back to the actual output; the reduced supreme gluing copy names a whole standard, not necessarily an original designated B-label. |
| Arbitrary replacement | `TrainArbitraryReplacementComplete`, `TrainArbitraryLegalReplacementComplete` | Construct real physical incidences, output linearity and any order-one designated-retention witness. These modules already handle global legality/acceptability/order and later supreme-label pullback at their stated scopes. |
| Fixed-target short replacement | `TrainShortOnlyPlanGlobal` | Use only after an actual designated occurrence of the source cycle has been identified and its `ShortValid` edge-membership premises proved. |
| Generated output geometry | `TrainSelectedPictureLinearPretrain`, `TrainSelectedPictureIntrinsicGeometry`, `TrainSelectedPictureStageGeometry` | Conditional complete wagon geometry and actual old-stage assembly are proved. Supply the genuine local witness and interior compatibility/girth inputs; positive-cut cycle transfer and full next-stage construction remain separate. See [the intrinsic geometry ledger](TRACK_B_INTRINSIC_GEOMETRY_2026-10-30.md). |
| All adjacent train parameters | `TrainAllAdjacentParametersBridge`, `TrainAllAdjacentParameterPreservation` | Supply actual old/core parameters, shared compatibility and the required interior cycle/bridge bounds. Do not rebuild the quotient transport. |
| Filling | `TrainFillingCarrierInvariant` | Full system-girth and designated-subcopy restriction; carrier equalities alone do not prove either. |
| Rank and recursion | `TrainCutoffWellFounded`, `TrainCutoffLexRank` | Forest-to-supreme conversion and the recursive witness-existence theorem. The well-founded rank is already proved. |

## Validation discipline

Keep physical edge labels, designated labels and quotient wagon labels distinct. Do not infer equality of wagon labels from equality of vertex carriers, infer strongness of a union from strongness of its constituents, or prune uncovered edges in higher train coordinates. Preserve the explicit `PlanProducesBigCycle` obligation.

Run the all-module build, every `Check*.lean` axiom audit, and the finite regressions on the exact proposed head. The source inventory is a discovery aid, not a Lean parser, an exhaustive semantic audit or permission to delete unused-looking modules. Manuscript marks remain compact, colored, clickable margin signs; no identifiers need be printed in the margin.
