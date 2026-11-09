# Compact direct private-extension validation

Date: 2026-11-09. Worktree: `lean-girth-compact`, branch
`validation/compact-diagram-20261109`. This checks the direct disjoint-sum
construction in `paper/16-cutoff-two.tex`.

## Finding and repair

The previous `UniformPrivateTemplate.toPrivateWagonInput` requires an
equivalence from **every** first wagon to the same full template W.
`exists_colouredRamsey_indexedPrivateChoices` repeats that premise.
Those results do not instantiate the compact proof's actual choice
`W = Σ p, F_p`. The old verification markers therefore overstate what
was checked for this paragraph.

`Girth/CompactPrivateExtension.lean` supplies the direct replacement.
For arbitrary old vertex carriers F_p and their covered edge families,
it defines the disjoint-sum edge family by actual tagged images. A
strong selected embedding of the sum into X is restricted to F_p by
`coordinate p x = star ⟨p,x⟩`.

The key proof is `restricted_strong`: an ambient edge meeting the
p-th coordinate range twice comes from some sum edge by global
strongness. That edge has a summand tag q. One of the common vertices,
injectivity of `star`, and equality of Sigma first coordinates give
q = p. Thus the edge belongs to p's selected local edge set.

This genuinely proves the missing local strongness condition. It does
not assume strongness, coverage, or intersection geometry of the
resulting private extension.

## Checked declarations

| Declaration in `CompactPrivateExtension` | Result |
| --- | --- |
| `restricted_strong` | Strongness of the chosen sum copy restricts to each summand, retaining its correct edge label. |
| `toPrivateWagonInput` | Constructs all fields of the old private-extension input from the sum and local coverage. No `F_p ≃ W` premise. |
| `toPrivateWagonInput_coordinate` | The coordinate is literally the restriction `star ⟨p,x⟩`. |
| `selected_edge_carrier` | A selected local edge is exactly the original physical edge on the old vertices, after the `Sum.inl` inclusion. |
| `componentGeometry` | Derives the three private scattering fields for every parent map on first-wagon labels. |
| `range_inter` | Proves the exact physical identity `range(place p) ∩ range(place q) = inl '' (F_p ∩ F_q)` for p ≠ q. |
| `sum_support_covered` | Derives support coverage of W from coverage of its summands and its actual support identity. |
| `ofStrongEmbedding` | Takes an actual relational embedding `c : W → R` and `AStrong A R (copyCarrier c)`, and returns the direct private input. |
| `ofStrongEmbedding_coordinate` | The resulting relational coordinate is literally `c ⟨p,x⟩`. |

The first seven geometric declarations may be used directly for the
hypergraph disjoint sum. The relational constructor also takes the
explicit identification
`supportCopies A W = sumEdges oldCarrier wagonEdges`.
This states that W's actual relational support is the intended disjoint
sum; it is not an assumed property of the output private extension.

## Kernel validation

Lean 4.35.0-rc3 compiled the new module and its focused check successfully.
The three uncached old imports were compiled first:
`TrainDesignatedSubcopyLocalSupreme`, `TrainFillingPrivateExtension`,
and `TrainFillingPrivateUniform`. The only old-module diagnostics were
existing `dif_pos`/`dif_neg` deprecation warnings.

All final commands used the verified runtime, an explicit `LEAN_PATH`
containing this worktree's objects and the cached dependency objects,
and `/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh`.
No Mathlib source rebuild was used. An initial Lake invocation created
the ignored manifest and started Mathlib's cache download hook; it was
interrupted, and all compilation then used direct Lean.

Focused commands (after runtime and `LEAN_PATH` setup):

```sh
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lean \
  Girth/CompactPrivateExtension.lean \
  -o .lake/build/lib/lean/Girth/CompactPrivateExtension.olean
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lean \
  CheckCompactPrivateExtension.lean
```

Both exited 0. `CheckCompactPrivateExtension.lean` prints axioms for all
nine declarations. The only reported axioms are `propext`, `Quot.sound`,
and, for the concrete private placement and relational factorization,
`Classical.choice`. `sum_support_covered` is axiom-free. There is no
`sorryAx`, added axiom declaration, or admitted proof. The complete
output is `private-extension-axioms.log` beside this report.

The strict repository audit also passed:

```sh
python scripts/check_axioms.py \
  checks/compact-diagram-20261109/private-extension-axioms.log \
  CheckCompactPrivateExtension.lean
```

It reported: `Checked 9 declarations; only the standard logical axioms occur.`

## Exact scope and remaining work

This closes the direct **local private-extension geometry** gap caused
by replacing uniformization with the disjoint wagon sum. It validates
the sentence that each F_p is strong in its private X_p, its pointwise
target-edge coverage, the exact cross-wagon intersection, and the
physical restoration of each selected old edge.

It does not prove a prescribed-A1 Ramsey witness, the trimming step,
the ordered relational support identity for the particular chosen W,
or a direct analogue of the complete EHN indexed-choice existence
theorem. It does not build global G0, contract it, identify the selected
M-copy inside H, transport restored wagon quotients, or prove the final
target-labelled Ramsey arrow. Those conclusions must retain their
separate open markers or cite separate verified results.

The English direct construction is sound at this local interface and
does not need to reintroduce a uniform enlargement. Its verification
marker should cite `CompactPrivateExtension.ofStrongEmbedding` together
with `componentGeometry`/`range_inter`, while stating the relational
support identification premise if the stronger relational claim is
made. The old indexed-choice existence theorem should not be presented
as already producing this new summand-restricted family.
