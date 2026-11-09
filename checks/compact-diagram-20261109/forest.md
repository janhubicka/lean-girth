# Compact diagram forest validation

Validated locally on 2026-11-09, on branch
`validation/compact-diagram-20261109`, based on
`2f900df5b3ee3c32e6471f143dd720bfea27781a`.

## Result and exact scope

`Girth/CompactDiagramForest.lean` proves the substantive join-tree bridge for
the revised Section 4 forest definition. Let `F` be a labelled family of
`HypergraphPiece`s, let `E` be an ambient `LinearEdgeSet`, and assume every
edge of every piece belongs to `E`. For an existing `JoinTree F`, allowed
full intersections on its graph links imply `PairwiseAllowed F`, hence the
existing `ForestOfCopies F` predicate.

The proof does **not** assume the desired non-adjacent intersection property.
It first derives point membership along the unique tree path from the
existing induced-occurrence connectivity field `JoinTree.running`. For a
non-subsingleton intersection of two distinct endpoint pieces, the first and
last link separators are physical edges containing every common point.
Ambient linearity forces these two edges to agree. That edge belongs to both
endpoints and equals their entire carrier intersection.

Declarations in namespace `StructuralRamsey.Girth`:

| Declaration | Proven conclusion |
|---|---|
| `JoinTree.compact_mem_carrier_of_mem_path` | Every common endpoint point belongs to every piece on the unique path. |
| `JoinTree.pairwiseAllowed_of_linkAllowed_of_linear` | Allowed link overlaps imply all-pairs allowed overlaps. |
| `JoinTree.forestOfCopies_of_linkAllowed_of_linear` | The compact hypotheses imply the existing `ForestOfCopies` API. |
| `JoinTree.edge_occurrence_preconnected_of_linkAllowed_of_linear` | Occurrences of a physical edge with at least two distinct points are preconnected, as actual piece-edge membership. |
| `forestOfCopies_iff_empty_or_linkAllowed_joinTree_of_linear` | The existing forest predicate is equivalent to the link-local join-tree condition, including the empty-family convention. |

The statements need no finiteness assumptions; they apply in particular to
the finite manuscript setting. Edge-occurrence preconnectedness permits the
edge to have no occurrences. When it has an occurrence, the induced graph
is connected; acyclicity is inherited from the ambient tree.

This work does not formalize a free quotient, quotient faithfulness, or
reflection of relations by chart maps. The English equivalence between free
tree realization and running intersection remains outside these Lean
statements. These proofs also do not establish the local partite existence
theorem or any completion/lifting step.

## Finite regression

`CheckCompactDiagramForest.lean` includes an explicit three-member example on
four ambient points. Its two leaf charts have the distinct 3-edges
`{0,1,2}` and `{0,1,3}`; the central chart has all four points and both edges.
The star is a genuine `JoinTree`, and all its links have allowed full edge
intersections. Its leaves intersect in `{0,1}`, which is not a whole edge of
either leaf, so the family is not a forest.

The check proves `links_allowed`, `leaves_not_allowed`,
`ambient_not_linear`, and `not_forest`. Thus dropping ambient linearity would
make the claimed bridge false, even for two uniform 3-edges and a finite
three-node tree with running intersection.

## Local commands and outcomes

The local runtime smoke returned:

```text
Lean (version 4.35.0-rc3, x86_64-unknown-linux-gnu,
commit 470d5ce1400764999581fd26d5d72b00d990b0f4, Release)
```

From `/workspace/scratch/095f642caf71/lean-girth-compact`:

```bash
source /workspace/scratch/095f642caf71/runtime/env.sh
export LEAN_PATH=".lake/build/lib/lean:$(find -L .lake/packages -maxdepth 5 -path '*/.lake/build/lib/lean' -type d | paste -sd:)"
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lean -o .lake/build/lib/lean/Girth/CompactDiagramForest.olean Girth/CompactDiagramForest.lean
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lean CheckCompactDiagramForest.lean
```

Both final commands exited 0, with no warnings or errors. The module was
compiled to a fresh local `.olean` before the check imported it. The check
printed all five theorem signatures and their axiom dependencies. Every
main theorem has precisely the standard dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

The finite regression's `leaves_not_allowed` uses only `propext`;
`ambient_not_linear` uses the three standard dependencies above; and
`not_forest` uses `propext` and `Quot.sound`. No `sorryAx`, new axiom, or
native-decision axiom occurs.

The `#print axioms` commands use fully qualified declaration names. A fresh
run was saved to `/tmp/compact-diagram-forest-audit.log` and passed the strict
repository checker:

```bash
python scripts/check_axioms.py /tmp/compact-diagram-forest-audit.log CheckCompactDiagramForest.lean
```

```text
Checked 8 declarations; only the standard logical axioms occur.
```

No global files, dependency sources, dependency build outputs,
`Girth.lean`, or `lakefile.toml` were changed. Existing dependencies and
their build cache were reused. All Lean processes used the specified
two-slot wrapper and `LEAN_NUM_THREADS=1` from `runtime/env.sh`.
