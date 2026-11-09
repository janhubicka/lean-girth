# Initial-picture validation

Date: 2026-11-09. Base: `2f900df5b3ee3c32e6471f143dd720bfea27781a`.
Worktree: `lean-girth-compact`, branch `validation/compact-diagram-20261109`.

## Claim and new bridge

The compact paper's `lem:picturezero` is in
`paper/10-cycle-conditions.tex`; its two conclusions are used together by
`paper/14-conversion.tex` and `paper/17-induction.tex`.

`Girth/CompactInitialPicture.lean` supplies:

- `TrainRecursiveWitness.initial_bottomSystemGirth_of_supportGirth`:
  ordinary target support girth implies full system girth at the actual
  initial bottom cut. The bottom train relation is equality of physical
  edges, so its quotient labels are injectively identified with those edges.
  Thus the labelled bottom-cut hypothesis required by the existing initial
  system theorem is derived, rather than assumed separately.
- `TrainRecursiveWitness.initialPicture_systemGirth_and_mixedForest`:
  for the same literal initial picture and selected component copies,
  **all proper-cut full system-girth bounds, including the bottom**, and
  **the complete mixed forest bound through the head cutoff** hold together.

The joint theorem's hypotheses are a nonempty cutoff list whose entries
are at least two, ordinary target support girth at its head, and labelled
target wagon-cut girth at its positive coordinates. The structural inputs
are a nonempty irreducible source, a nonempty finite target carrier, and a
nonempty prescribed base family. The base family need not be finite.
There is no initial system-girth, mixed-forest, or finished-stage hypothesis.

## Reused scope

The bottom mixed forest is already proved exactly by
`ForestRecursiveInitialMixed.initialSelected_mixedForest`. This validation
does not claim to introduce that geometric proof. Its underlying
`forest_selected_embeddedTarget_of_girthGT` handles both local cases:
an actually selected component centre gives the existing star; if that
centre is absent, the selected distinct one-edge pieces form a forest by
target support girth. Disjoint component lifting joins the local forests.
It never adds a centre and then removes it from an arbitrary join tree.

The forest quantifier is `FiniteMixedForestThrough`: finite sets of distinct
complete pieces consisting of every ambient A-edge and the literal selected
B-components. It is not a claim about arbitrary repeated multi-edge labels.
Irreducibility factors every ambient initial A-copy through a component.

The system proof reuses
`TrainRecursiveInitialTailSystem.initialTrain_fullSystemGirth_of_targetCut`.
That theorem derives physical pretrain linearity, localizes cycles to one
component at a proper cut, retains all occurrences of a present designated
label with the literal identity replacement plan, and excludes edge-only
cycles using labelled target-cut girth and the source-order budget.

The new bottom bridge combines
`physicalASupport_labelledGirth_of_girth`,
`EdgeTrainLevels.bottom_labelledCutGirth_of_edgeGirth`, and that initial
system theorem. The joint theorem splits coordinate zero from positive
coordinates and adds the exact existing mixed-forest theorem. This closes
the interface gap between the existing positive-tail stage constructor and
the paper's joint all-coordinate picture-zero conclusion.

## English simplifications and boundaries

1. Say “At every proper cut, a cycle stays in one component.” The universal
   top merges components and is not one of the vector's tested coordinates.
2. Keep the short centre-present / centre-absent split for bottom forests.
   It explains why no forest-heredity or centre-deletion argument is needed.
3. Monotonicity of the cutoff vector, target support coverage, and adjacent
   parameter bounds are unnecessary for these two picture-zero conclusions.
   They belong to other stage fields or later recursion.
4. No two-edge target hypothesis is needed here. The system bound is proved
   directly; the forest-to-supreme theorem's two-edge restriction is not used.
5. This verifies initialization, not the geometric successor operator,
   the complete forest-to-order conversion, or the full recursive theorem.

## Validation

**PASS.** The new module compiled, and `CheckCompactInitialPicture.lean`
compiled with exit code 0. Both new theorems and four reused declarations
were audited by their fully qualified names. The repository checker reports:

```text
Checked 6 declarations; only the standard logical axioms occur.
```

Every audited proof depends only on a subset of `propext`,
`Classical.choice`, and `Quot.sound`. No `sorryAx` or additional axiom occurs.
A token scan also found no `sorry`, `admit`, or `axiom` declaration in either
new Lean file.

Logs:

- `initial-picture-build.log`: targeted missing-import compilation and the
  new module build. Existing source dependencies produced only linter or
  deprecation warnings; the new module produced none.
- `initial-picture-check.log`: checked theorem signatures and all six
  `#print axioms` results.

The axiom audit command was:

```sh
python scripts/check_axioms.py \
  checks/compact-diagram-20261109/initial-picture-check.log \
  CheckCompactInitialPicture.lean
```

Lean 4.35.0-rc3 was invoked after sourcing `runtime/env.sh`, always through
`runtime/with-lean-slot.sh`, under the shared two-worker / 8-GiB cgroup
limit. Final builds used direct `lean` with explicit `LEAN_PATH` containing
this worktree's output directory and the existing package output directories:

```sh
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lean \
  -o .lake/build/lib/lean/Girth/CompactInitialPicture.olean \
  Girth/CompactInitialPicture.lean
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lean CheckCompactInitialPicture.lean
```

Only missing local `Girth` imports were compiled. No global target,
Mathlib rebuild, shared dependency edits, or changes to the ongoing
`lean-girth` checkout were part of this validation. An initial optional
`-M3000` limit failed during the `Mathlib.Tactic` import before proof checking;
removing that extra limit, while retaining the runtime's cgroup and slot
limits, resolved the infrastructure failure. No proof source was changed
to bypass it.

SHA-256:

```text
2b8f4334397e71401db91dc8d78a1d389f62c855e961f10a9ace83fd547aad68  Girth/CompactInitialPicture.lean
085de130426114a48aaa4477ffdb9a6b493261e04f0f26180af45041544f5d2d  CheckCompactInitialPicture.lean
```
