# Binary forest gluing without auxiliary vertex members

Validated locally on 2026-11-09 in the dedicated compact-diagram checkout,
using Lean 4.35.0-rc3 and the existing dependency cache.

## Proven component

`Girth/CompactForestGluing.lean` proves a binary gluing step for two genuine
finite forests in a common linear ambient edge family. Its output is
`ForestOfCopies (sumPieces F G)` on exactly the labels `I ⊕ J`.
No singleton point is inserted as an additional member.

The three declarations are in `StructuralRamsey.Girth`:

| Declaration | Inputs beyond the two forests and their linear ambient edge family |
|---|---|
| `forestOfCopies_sumBridge_of_allowed_connectors_of_linear` | Two existing connector labels; every point occurring on both assembled sides belongs to both connectors; the full intersection of those two connectors is allowed. |
| `forestOfCopies_sumPieces_of_subsingleton_union_overlap_of_linear` | Both label types are nonempty; the intersection of the two assembled carrier unions is subsingleton. |
| `forestOfCopies_sumPieces_of_common_edge_anchors_of_linear` | Existing anchors on both sides have carrier `e` and contain `e` as a piece edge; the intersection of the two assembled carrier unions is contained in `e`. |

None of these inputs assumes allowed intersections for all cross-side member
pairs. The proof constructs the existing `JoinTree.sumBridge`, checks its
old internal links using the two forest certificates and its unique new
link using the connector hypothesis, then invokes
`JoinTree.forestOfCopies_of_linkAllowed_of_linear` from the preceding
compact-diagram module.

For a nonempty singleton overlap, the second theorem chooses any member
containing that point on each **assembled side**. If the overlap is empty,
it joins arbitrary existing members. The choice does not require that the
point occur in a local family at an intermediate outer owner. This is the
binary ingredient needed for the suggested outer-leaf induction; it avoids
the invalid prescription of choosing one point-carrying anchor at every
outer owner.

For the full-edge case, the third theorem only requires the properties of
retained one-edge requests that the gluing proof uses: their carriers are
exactly `e`, and `e` is an actual member edge on both sides. It is therefore
slightly more general than requiring their entire edge sets to be `{e}`.

The singleton-overlap theorem explicitly assumes both label types are
nonempty. The core and full-edge theorems instead take chosen labels, which
already imply that condition. Empty-side elimination and the full outer-tree
leaf induction have not been formalized in this file. This is a proved
binary assembly component, not a claim that the entire revised join-tree
lifting theorem or its completion step has been formalized.

## Concrete checks

`CheckCompactForestGluing.lean` contains two successful applications:

- Two two-point, edge-free charts on `{0,1}` and `{1,2}` are joined along
  their common point. The resulting family has exactly two labels, with
  vertex `1` used only as the intersection label of a join-tree link.
- Two retained one-edge charts carrying the same two-point physical edge
  are joined along that full edge.

The file prints the three theorem types and audits those three theorems,
the two regression proofs, and the two-label cardinality statement using
fully qualified declaration names.

## Commands and result

From `/workspace/scratch/095f642caf71/lean-girth-compact`:

```bash
source /workspace/scratch/095f642caf71/runtime/env.sh
export LEAN_PATH=".lake/build/lib/lean:$(find -L .lake/packages -maxdepth 5 -path '*/.lake/build/lib/lean' -type d | paste -sd:)"
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lean -o .lake/build/lib/lean/Girth/CompactForestGluing.olean Girth/CompactForestGluing.lean
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lean CheckCompactForestGluing.lean > /tmp/compact-forest-gluing-audit.log
python scripts/check_axioms.py /tmp/compact-forest-gluing-audit.log CheckCompactForestGluing.lean
```

All commands exited 0. The final module build and check had no warnings or
errors. The strict checker reported:

```text
Checked 6 declarations; only the standard logical axioms occur.
```

All six declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`. No `sorryAx`, custom axiom, or native-decision axiom occurs.
The earlier `CheckCompactDiagramForest.lean` was also corrected to use fully
qualified axiom names, rerun locally, and passed the strict checker for all
eight of its declarations.

Only the new modules/checks and their validation notes were written. No
existing public import aggregator, lake configuration, dependency source,
dependency build cache, global runtime file, or ongoing `lean-girth`
checkout was changed. Lean commands used the prescribed two-slot wrapper
and `LEAN_NUM_THREADS=1`.
