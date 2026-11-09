# Coherent binary overlap realization — local Lean validation

Date: 2026-11-09.

## Scope and result

`Girth/ACopyOverlapRealization.lean` proves the point-set portion of manuscript
`paper/03-partite-construction.tex`, Lemma `binaryrealization`. It is a new,
standalone module; the main import file and existing modules are unchanged.

The interface `StructuralRamsey.Girth.CoherentOverlap Ω K` gives each pair
label by its graph `Rel e f a b` and assumes only:

1. `Rel e e a b ↔ a = b`;
2. `Rel e f a b → Rel f e b a`;
3. `Rel e f a b → Rel f g b c → Rel e g a c`.

These are the three manuscript coherence laws in graph form. Functionality and
inverse functionality are derived, rather than assumed. The explicit
`overlapEquiv` between the domain and range, together with
`overlapEquiv_eq_iff`, certifies that this graph interface describes partial
bijections. No quotient-injectivity or exact-overlap conclusion is a hypothesis.
No finiteness hypothesis is needed.

## Exports

All names below are under `StructuralRamsey.Girth.CoherentOverlap`, except the
structure `StructuralRamsey.Girth.CoherentOverlap` itself.

| Export | Content |
| --- | --- |
| `refl`, `reverse_iff` | Elementary consequences of coherence |
| `right_unique`, `left_unique` | Partial-function and inverse partial-function uniqueness |
| `domain`, `range` | Domain and range sets of pair labels |
| `overlapEquiv` | Explicit equivalence between each label's domain and range |
| `overlapEquiv_rel`, `overlapEquiv_eq_iff` | The recovered partial bijection has exactly the original graph |
| `occurrenceSetoid` | Coherence makes the occurrence relation an equivalence, without taking a larger closure |
| `Point`, `nodePoint` | Occurrence quotient and its node-coordinate maps |
| `nodePoint_eq_iff` | Cross-node quotient equality is exactly the specified label |
| `nodePoint_injective`, `nodeEmbedding` | Every node embeds as a point set |
| `carrier` | Realized point carrier of a node |
| `nodePoint_mem_carrier_iff` | Membership in another carrier is exactly membership in the overlap domain |
| `carrier_inter` | Carrier intersection is exactly the first node's image of the overlap domain |
| `point_covered` | Every quotient point lies in a node |
| `Linear` | Distinct-node overlap domains are subsingleton |
| `linear_carrier_inter`, `linear_iff_carrier_inter` | Exact equivalence of diagram linearity and subsingleton realized intersections |
| `carrier_injective_of_linear`, `carrier_eq_iff_of_linear` | With `Nontrivial K`, linearity makes distinct nodes have distinct carrier sets |
| `carrierRangeEquiv`, `carrierRangeEquiv_val` | With `Nontrivial K` and linearity, nodes are bijective with the range of their carrier sets, preserving each carrier |
| `ofCharts` | Encoding actual injective charts by ambient equality |
| `toAmbient`, `toAmbient_nodePoint` | Quotient evaluation and its value on every coordinate |
| `toAmbient_injective` | Evaluation of an actual-chart encoding is injective |
| `mem_range_toAmbient_iff` | Evaluation's image is exactly the union of chart point images |
| `toAmbient_surjective_iff` | Evaluation is surjective exactly when the charts cover the ambient type |
| `ambientEquiv`, `ambientEquiv_nodePoint` | A covering family reconstructs the ambient point type, commuting with all chart maps |
| `of_nodeEmbeddings_rel_iff` | Encoding the realized node embeddings returns exactly the original binary labels |

## Validation

Toolchain: Lean 4.35.0-rc3. Dependencies were already copied into this isolated
checkout. Commands were run after sourcing
`/workspace/scratch/095f642caf71/runtime/env.sh`, using the shared two-slot
wrapper `/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh`:

```sh
lake env lean -DwarningAsError=true Girth/ACopyOverlapRealization.lean \
  -o .lake/build/lib/lean/Girth/ACopyOverlapRealization.olean
lake env lean -DwarningAsError=true CheckACopyOverlapRealization.lean
python3 scripts/check_axioms.py \
  checks/a-copy-foundations-20261109/overlap-axioms.log \
  CheckACopyOverlapRealization.lean
```

All commands exited zero. The Lean source compiled without warnings; Lake
prints the known pre-existing batteries working-tree warning caused by the
runtime compatibility patch. There were no package updates or global builds.

- `overlap-compile.log`: clean targeted compilation.
- `overlap-axioms.log`: `#print axioms` output for 21 core declarations.
- `overlap-strict-axioms.log`: strict checker success for all 21 declarations.

Only `propext`, `Classical.choice`, and `Quot.sound` occur. No `sorry` or new
axiom declaration occurs in either new Lean file.

## Remaining relational-faithfulness gap

This is a point-set realization result, not a relational reconstruction theorem.
It does not encode relation symbols, tuples, order, parts, unsupported chart
occurrences, or the requirement that pair maps are induced-subchart
isomorphisms. Accordingly it does not prove that a union of chart relation
records reflects relations on each chart, or that all physical copies in the
result are exactly its specified nodes. That requires the separate decorated
reconstruction and chart-coverage arguments in the manuscript.

For the manuscript's physical types with at least two points, the
`Nontrivial K` results remove any duplication of specified carrier sets:
`carrierRangeEquiv` identifies nodes bijectively with exactly the range of the
carrier map. This proves exact node labels for the specified hyperedge family.
It still does not prove that every relational A-copy is specified. Without
`Nontrivial K`, coherence and linearity permit two singleton nodes with equal
carriers. `ambientEquiv` recovers all points only under its explicit
chart-coverage hypothesis; the unconditional result `mem_range_toAmbient_iff`
recovers precisely the supported point union.
