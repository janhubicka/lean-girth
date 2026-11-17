# Numbered Track 2 — current proof chain and validation ledger

**Status (17 November 2026): source-level candidates, NOT kernel-verified.**
Scope: the circulation part of the girth manuscript, excluding the appendix.
The historical exploratory branches and prior validation notes remain in Git history;
this file records only the currently retained argument.

## Working branches and provenance

- Lean: [`validation/2-physical-copy-girth-20261117`](https://github.com/janhubicka/lean-girth/tree/validation/2-physical-copy-girth-20261117), transplanted on 17 November onto `lean-girth/main@cd76b3ba6d43b7095a72dd53de972b754b36389e`.
- Manuscript: [`edit/track2-physical-copy-20261117`](https://github.com/janhubicka/girth/tree/edit/track2-physical-copy-20261117), transplanted on 17 November onto `girth/main@5c8142c9e499dc3b1f734f6b7987a708eb0f3809`. The paper's newer Track 1 validation annotations in `paper/07-forest-increment.tex` are preserved.
- The circulated historical reference `girth@8c9cfa6e` is separate from both active branches. No changes described here are merged into `main`.

## Mathematical proof and exact interfaces

| Obligation | New source or reused declaration | Key assumptions / conclusion |
| --- | --- | --- |
| Trace acyclicity (`lem:foresttracegirth`) | `ForestTraceAcyclic.girthGT_union_of_forest_edge_traces`, `girthGT_selected_of_forest_edge_traces` | Forest of labelled pieces; each member's trace on a linear active hypergraph is subsingleton or a full active edge; active edges have size ≥2. Retain those trace edges, reuse the original join tree, then apply the existing `girthGT_union_of_forest`. |
| Bounded-cycle contradiction | `ForestActiveTraceGirth.girthGT_of_bounded_trace_forest_completions` and boundary-specialized version | Use the *already injective* Berge-cycle edge map indexed by `ULift (Fin c.length)`, as in the existing `ForestRecursiveOutputGirth`. No separate subtype/image cardinality argument is required. |
| Actual old active girth (`lem:puresubsystem`) | `ForestCompletionTraceBridge`, `ForestActiveTraceBoundary`, `ForestOldActiveGirth`, `ForestCopySetCompletion`, `ForestOldActiveSetGirth`, `ForestCompletionTwoEdgeLinearity` | Start from finite SETS of actual A and designated B-copy labels; each maps to its complete A-support, possibly noninjectively. The selected active A-edges are whole traces; only newly added designated B-pieces require boundary classification. For `m ≥ 2`, completing pairs of one-edge supports already gives old A-linearity; no separate old-linearity premise is needed by the final endpoint. Return girth of the **old induced active subsystem**, not the processed output. |
| General join-tree lift (`lem:joinlift`) | `ForestSeparatorCrossAllowed`, `ForestBinarySeparatorLift`, `ForestGeneralJoinLift`, `ForestDuplicateLabelNormalization`, `ForestDuplicateLabelGeometry`, `ForestRetainedSetLift` | At an empty/singleton outer separator, connect local forests without any support-edge request. At a full-edge separator, bridge the two retained one-edge requests. Nonempty local members and ambient linearity ensure any duplicate *underlying* member is one-edge, so delete only duplicate one-edge labels and omitted requests. The exact finite retained family may include requests that are selected or added and therefore must be kept. Includes the empty outer-family case. |
| Direct forest increment (`lem:forestincrement`) | **REUSE EXISTING** `ForestRecursiveOutputGirth.actualPartiteDesignatedAB_forest_and_girth_of_localGeometry` | The existing theorem derives old and core A-linearity, output girth-two, and local gluing strongness for `m > 2`; strongness at `m=2` is explicit. It then proves the actual mixed-forest increment and the stronger ordinary girth bound through `m`. This replaces two redundant, newly written Lean modules and three uncompiled theorems. The actual local Ramsey witness is still a separate assumption. |

### Correspondence checks

- The manuscript's forest-extension property is over **sets of actual relational copies**, not embedding labels. `ForestPhysicalCopySetCompletion.PhysicalCopySetForestExtension` now records a finite set of physical copy keys and a forest on its image of DISTINCT complete support pieces. `ForestPhysicalABCompletion` defines the physical key as a tagged A-carrier/B-carrier and proves that `pictureABLabelSupport` factors through that key. Its theorem `oldActiveInduced_girthGT_of_physicalCopySetExtension` derives old active girth from the faithful physical-set completion property, using the existing labelled-to-indexed adapter internally. Neither the label-to-physical map nor the physical-to-support map is assumed injective. The two tags must be checked against the manuscript's union of physical A/B-copies when A and B might describe the same underlying substructure; the main nontrivial case distinguishes these sorts.
- The outer forest's join tree transfers to full pieces because pairwise intersections are exact. For large separators, the request is the complete common edge in both members' **own support**, not merely a carrier subset. For singleton separators, no helper member is needed.
- Duplicate local member labels are safely deleted only after proving that any duplicated piece is one-edge; deleting an arbitrary designated B-piece can destroy foresthood.
- Old `A`-linearity at `m≥2` follows from the pair-completion property. At `m=1` this is false: `{0,1,2}` and `{0,1,3}` are non-linear but every singleton request can be a forest.
- Generation of the active subsystem still uses the partite projection, base linearity/rigidity, and coverage of irreducibles. For nonpruned local witnesses the existing `ForestMixedIrreducibleCoverage` / `ForestMixedActiveGenerated` B-or-A alternative may be necessary; it must not be confused with Track 2's active-girth conclusion.
- The larger-cutoff local Ramsey witness, full stage assembly, and any missing hypotheses in the paper-to-Lean instantiations remain obligations for the other numbered tracks. Existing conditional theorems do not construct those witnesses.

## Verification inventory and reproducible gate

The current branch contains **16 new implementation modules with 33 new theorem candidates**:
17 in the active-girth/physical-copy bridge and 16 in the general lifting chain.
The direct-increment component uses **four existing declarations** in `ForestRecursiveOutputGirth.lean`, not new proof candidates.

| Strict axiom gate | Theorems audited |
| --- | ---: |
| `Girth/CheckTrack2ActiveGirth.lean` | 17 new |
| `Girth/CheckTrack2DirectIncrement.lean` | 4 reused |
| `Girth/CheckTrack2JoinLift.lean` | 16 new |
| `Girth/CheckTrack2Trace.lean` | 37 total |

From a real checkout with the repository-pinned Lean/Lake/Mathlib cache restored:

```bash
bash scripts/check_track2_local.sh active
bash scripts/check_track2_local.sh join
bash scripts/check_track2_local.sh increment
bash scripts/check_track2_local.sh all
```

The runner builds the requested module, elaborates its exact `#check` and
`#print axioms` declarations, and calls the existing strict
`scripts/check_axioms.py` (allowing only `propext`,
`Classical.choice`, `Quot.sound`). The full check runs only
after the three independent gates pass.

**Checks actually available here:** static source audits (balanced simple
delimiters, no explicit `sorry`/`admit` in the 14 new modules, no missing
or duplicated axiom probes). The container has no `lean`, `lake`,
`elan`, pinned Mathlib build cache or outbound GitHub DNS. Therefore
**none of the 33 new theorem bodies has been compiled or axiom-audited**.
Do not promote any new `\leanverified` marker or merge the candidate.

## Bounded diagnostics, not theorem certificates

The manuscript branch records executable Python checks
`validation/numbered-tracks/check_trace_and_singleton.py`,
`check_cross_separator.py`, `check_binary_separator_gluing.py`,
`check_three_owner_join_lift.py` and `check_four_owner_join_lift.py`.
Earlier executions found no counterexample in 407 triangle, 667 square
and 45 pentagon trace configurations; 144 cross-separator configurations;
7,224 singleton/empty and 177 common-edge binary joins;
1,369 three-owner combinations; and 45,000 deterministic four-owner
combinations (with four one-edge-request deletion patterns each).
The negative controls show why local singleton connectors are not automatic,
why carrier inclusion does not supply an owned edge, and why one cannot
delete arbitrary multi-edge B-members.

### Completion criteria

Run the **actual** Lean gates and inspect printed axioms, repair source
errors at the first failing import, compare the elaborated theorem
statements against the manuscript's hypotheses, and check the exact
selected/added family classification at the real partite step.
Only then update the validation markers. The general local
Ramsey-witness existence and complete recursive construction remain
outside Track 2.

## 17 November — physical-copy (rather than embedding-label) correction

The previous source predicate `FinsetLabelForestCompletionProperty` was
a convenient abstract intermediate but not literally the paper's invariant:
multiple embeddings can represent one physical B-copy. A labelled forest
cannot duplicate a multi-edge B-piece, even though the finite SET of
physical copies contains just one B-copy. Such duplicates must be collapsed
**before** requesting a forest completion.

`ForestPhysicalCopySetCompletion.lean` now encodes the actual manuscript
quantifiers: for each finite set `s` of physical copies of size ≤m, choose
a finite set `t ⊇ s` with all extra copies designated and with
`ForestOfCopies` on the finite image `t.image support` of DISTINCT
complete support pieces. The generic `toLabelFinset` transport takes
`s := labels.image key`, so its cardinal does not exceed the number
of selected embedding labels. No cloning of B-pieces is ever needed.

`ForestPhysicalABCompletion.lean` specializes the abstract physical
keys to tagged A-carriers and B-carriers. The full support of a B-carrier
is **all** ambient embedded A-copy edges contained in that carrier;
this depends only on the carrier, not on its embedding presentation.
These geometric equalities are explicit candidate theorems.
`oldActiveInduced_girthGT_of_physicalCopySetExtension` composes
physical-set extension → labelled-set extension → indexed support
completion → old active girth. As elsewhere, the m≥2 assumption
already yields ambient A-linearity from two-edge completion.

Important scope: the A/B tags are faithful when these are different
physical copy sorts, as in the nontrivial theorem case. In degenerate
cases where one underlying structure could be counted in both sorts,
a separate identification (or the theorem's trivial-case split)
is needed. **Do not silently count that object twice.**

All five new theorem declarations have unexecuted strict axiom probes.
The source remains uncompiled; this is a repair of a mathematical
interface, not yet a Lean certificate.


**Why the A/B carrier tags are faithful in the nontrivial case.**
If B contains at least two DISTINCT physical A-copies, then
`|V(B)| > |V(A)|`: otherwise each copy uses the whole finite
carrier of B and, as an induced substructure, there can be only
one physical A-copy. Consequently a physical A-copy and a
physical B-copy cannot be the same underlying substructure.
This is the case used by the recursive construction; the paper
handles `|Copy(A,B)| = 1` separately. Thus the tagged sum
`Set X ⊕ Set X` does not double-count any actual A/B-copy
in the nontrivial construction.

**Concrete failure of embedding-label counting.**
`check_physical_copy_labels.py` uses a physical B-piece with
carrier `{0,1,2}` and two support edges `{0,1}` and `{1,2}`.
Two embedding labels of that SAME B-copy have a disallowed
three-vertex mutual intersection; a labelled two-member forest
is impossible, whereas its finite physical set has just one
member and is trivially a forest. This script was executed
locally and its assertions passed. It is a diagnostic for
the type-interface correction, not a general Lean certificate.
