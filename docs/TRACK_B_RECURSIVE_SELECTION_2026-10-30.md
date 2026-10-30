# Track B: actual selected copies and nontrivial recursive steps

Starting point: merged PR #694, `f05b08132b8fd90ca6e0c37a48cb279f1f6b51e9`.
Scope: the circulation proof; no appendix changes.

The intrinsic geometry theorem supplies A-linearity, pretrain linearity at
every cut, and strongness of complete generated wagons. This continuation
connects its incidence model to the actual selected family, assembles the
bottom forest invariants, and uses the identity step in the finite pass.
It does not claim the missing positive-cut cycle theorem or local-witness
existence.

## Indexed labels and actual selected copies

The attachment cycle model has designated labels `I × SelectedOld`.
`ForestTailStage` instead stores the set of actual transported
`DesignatedCopy` values. These types cannot be identified just because
some vertex carriers are equal.

`TrainSelectedPictureLabelEquiv` constructs the literal map and proves:

- Surjectivity is exactly the definition of `transportedSelectedCopies`.
- A selected old copy with two distinct A-support edges has a vertex outside
  the active subsystem, under finite A and strongness of its prescribed
  base copy. Otherwise the checked active-boundary theorem would identify
  its two support edges.
- That private vertex recovers the standard index. Injectivity of the
  standard embedding then recovers the actual old designated copy.
- Two distinct physical A-copies in the fixed target supply the two-edge
  premise for every selected old copy.
- Old selected support-piece injectivity gives output selected support-piece
  injectivity. Neither injectivity of the gluing-image family nor an output
  geometry assumption is added.

The result is a genuine equivalence of designated-label types. The
prescribed gluing indices remain distinct even when their core image
carriers coincide. The one-edge target is excluded from this equivalence:
its entire copy can lie in the active subsystem, losing the standard index.

## Full system-girth transport

`TrainDesignatedReindexGirth` proves invariance under a bijective reindexing
of designated labels. Vertices, physical edge labels, ownership and wagon
parents are fixed. A target cycle pulls back with identical connectors and
order; A1 preserves the designated sum tag, and A2/A3 retain all physical
incidence data and positions.

The existing literal physical-map theorem transports the entire
`HasSimultaneousSupreme` witness, including the globally legal replacement
word and its resulting genuine `BigCycle`. The inverse label equivalence
identifies the mapped cycle with the original target cycle.

`TrainActualSelectedOutputGirth` identifies the complete indexed incidence
record with the reindexed actual selected-copy record. Hence full system
girth has exactly the same cutoff in both presentations. This transfers a
bound once the cycle-transfer proof supplies it; it does not prove that
bound from geometry. Physical pretrain linearity is independent of the
designated labels and agrees even without the two-edge assumption.

## Bottom forest and selected strongness

`TrainSelectedPictureStageForest` consumes `stage.bottomForest` directly.
Its tested-piece predicate is exactly every ambient A-edge together with
the canonical transports of selected old B-supports. No unselected lift is
introduced, and no ambient edge is pruned.

For bottom cutoff `k = t.headD 0`, with `k ≥ 2`, the genuine remaining
local inputs include selected base strongness, a nonempty true active
source, and the appropriate local forest alternative. At k > 2 this is the
predecessor mixed forest bound, two distinct active support edges and
injectivity of the physical gluing support family, together with core
ordinary support girth greater than k. That predecessor forest already
supplies whole-image strongness.

Only at k = 2 does the new interface ask for an intrinsic local full
system-girth bound at some cut and cutoff at least two, from which PR #694
derives whole-image strongness. Its physical linearity also gives core
ordinary girth greater than two, so this is not a separate premise at k = 2.
The interface does not require an additional intrinsic bound at larger
bottom cutoffs. This conditional forest interface must not
be advertised as supplying an interior bound when the train has height one:
there is then no interior cut. The older explicit-strongness interface
remains available for that case.

The output conclusions are the actual canonical selected-family mixed
forest through k, ordinary support girth greater than k, and A-strongness
of every selected output B-copy. Output girth greater than two is derived
before applying the forest increment, so the proof is not circular.

## Skip all trivial physical fibres

`TrainRecursiveNontrivialFibre` connects the existing ordered-source
identity picture step to the finite-pass construction endpoints. A local
operator is now requested only when two projected A-copies have distinct
physical carriers. Empty and singleton physical fibres retain the entire
old stage, its selected family, train, forest and tail conditions.

For an abstract readiness predicate, its drop law is used precisely in the
skipped case. For `FirstRefinementReady`, the existing tail theorem supplies
that law automatically. The two distinct projected carriers also yield two
distinct genuine support edges in the induced active target. Thus a
nontrivial target is derived where the local operator is used.

The resulting Ramsey construction theorem is still conditional on actual
nontrivial local steps and their preservation of remaining-fibre readiness.
It is not the unconditional recursive witness-existence theorem.

## Validation and remaining work

All public exports have explicit `#print axioms` checks. The focused Track B
workflow includes the five new modules and Checks, alongside the prior
geometry suite. Complete exact-head focused and repository-wide CI are
required before merge, including all audit and post-job steps.

Still separate are actual local-witness construction, positive-cut global
cycle transfer, remaining-fibre refinability preservation, and assembly of
the complete next stage. The companion TeX changes clarify literal labels,
the forest cutoff split, and the nontrivial-fibre dispatch, with compact
proof links activated only after the complete Lean gate.
