# Generated layered star on basic node sets

Validated locally on 2026-11-09 in
`/workspace/scratch/095f642caf71/lean-girth-a-copy`, using published base
`191ac8a6d5fc99b7cf314ea1df7d8451949f666a` and its
`Girth/ACopyExactStar.lean` theorem.

## Input and construction

`Girth/ACopyLayeredStar.lean` handles the algebraic node/wagon hierarchy
described in `paper/09-trains.tex` and the nested-parent paragraph of
`paper/11-amalgamation.tex`.

`ACopyLayeredStar.Diagram` contains fixed core and indexed source node
types, fixed shared node maps, and Nat-indexed source setoids. Its hypotheses
are source nesting, preservation and reflection of each source relation by
the shared maps, and equality for the source relations at level zero.
It contains no output relation, output normal form, output parent, or
output preservation conclusion.

At each level `n`, `Step D n` is exactly the core source relation, the
indexed source relations, and the literal shared node identifications.
`Generated D n` is its actual `Relation.EqvGen` closure. `Wagon D n` is
`Quot (Step D n)`, whose equality is precisely that generated closure.

The basic glued node type is `Node D := Wagon D 0`.
`generated_zero_iff_shared` proves that its identifications are generated
by shared pairs alone: the original zero-level source relations add only
reflexive identifications. Core and standard node maps are proved injective.

Parents between wagon quotients are induced by identity on original raw
nodes. The derived level-`n` relation on the actual node pushout compares
their images under the parent from level zero. This does not introduce an
independent output relation: `nodeSetoid_mk_iff` proves that it agrees on
raw representatives exactly with `Generated D n`.

Finally, `nodeWagonEquiv` proves

```lean
Quotient (nodeSetoid D n) ≃ Wagon D n
```

so the classes of the relation on glued basic nodes are exactly the
generated wagon labels. No equality of point carriers is used to identify
classes or labels.

## Exact exports

All names below have prefix `StructuralRamsey.Girth.ACopyLayeredStar.`.

| Export | Proven content |
|---|---|
| `generated_zero_iff_shared` | The basic node quotient is the quotient generated solely by shared node pairs. |
| `step_nested`, `generated_nested` | The source nesting hypotheses imply nesting of the actual generated relations. |
| `generated_core_iff`, `generated_source_iff`, `generated_iff_normal` | The abstract exact-star theorem is instantiated at every cut, with exact source restrictions and the generated normal form. |
| `parent`, `parent_mk`, `parent_refl`, `parent_comp`, `parent_surjective` | Quotient parents are identity-induced, functorial across levels, and surjective. |
| `coreMap_injective`, `sourceMap_injective` | Every source wagon quotient injects into the generated wagon quotient. |
| `parent_coreMap`, `parent_sourceMap` | Generated parents commute with both core and standard quotient maps. |
| `contact_parent` | A contact witnessed by a shared node survives at every higher level. |
| `sourceMap_eq_coreMap_iff` | Equality of a source wagon image with a core wagon image is exactly the constructed class contact. |
| `parent_sourceMap_eq_coreMap_iff` | A parent source image is core exactly when the higher-level source class contacts that core class; no lower-level contact is required. |
| `nodeCore_injective`, `nodeSource_injective` | Original source basic nodes embed into the actual level-zero pushout. |
| `nodeSetoid_mk_iff`, `nodeSetoid_nested`, `nodeSetoid_zero` | The derived equivalences on actual glued nodes agree with generation, remain nested, and start with equality. |
| `nodeSetoid_core_iff`, `nodeSetoid_source_iff` | Exact source restrictions hold for the relations on the actual glued node type at every cut. |
| `nodeWagonMap_bijective`, `nodeWagonEquiv` | Quotienting the actual glued node type gives exactly the generated wagon labels. |
| `top_source_core`, `generated_top`, `top_subsingleton`, `nodeSetoid_top` | Universal core/source top relations and nonempty shared domains imply a universal generated top, on raw nodes and on the actual node pushout. |
| `uniqueTop` | With a nonempty core, the generated top quotient has exactly one class. |

The partial contact maps are the `SourceStar.contact` maps constructed
from the actual source setoids and shared maps. `contact_parent` transports
the same shared representative through the quotient parent maps; no
independently supplied contact compatibility is assumed.

## Simplification and remaining scope

Levels are natural numbers, and all theorems apply to any `m ≤ n`.
A designated `top : Nat` is used for the universal-top conclusions.
This avoids a general preorder or dependent finite-level interface.
For finite-height data, extending the top relation constantly supplies
the Nat-indexed presentation; a separate finite-index adapter is not
implemented here.

The shared maps are ordinary functions. Compatibility and bottom equality
are sufficient for all proved source-embedding conclusions; the manuscript's
additional injectivity of the shared-domain maps is therefore admissible
but unnecessary for these quotient assertions.

The nonempty-core hypothesis is used only to construct `Unique` at the top.
Universal generated top and top subsingleton statements do not assert
nonemptiness. This preserves the empty layered-diagram case.

This is the node/wagon hierarchy application of the source-star theorem.
It does not connect the same node set to a simultaneous point-occurrence
quotient, retained chart-point records, or physical support in an existing
realized train interface. It proves no point-carrier formula, physical
linearity, strong inducedness, train parameter bound, or cycle/girth bound.
Those remain separate application obligations. No manuscript marker was
changed by this task.

## Regression checks

`CheckACopyLayeredStar.lean` builds an explicit diagram with a Boolean core,
two Boolean source copies, and a singleton shared domain in each copy.
Each source shares only its `false` node with the core's `false` node.
Level zero is equality, and every positive level is universal.

The check proves:

- The source `true` child is private at level zero.
- It is unequal to every core wagon image at level zero.
- Its parent at level one is a core wagon image.
- The two nodes of a source remain distinct in the actual basic-node pushout.
- Those distinct nodes become equivalent at level one, while remaining
  inequivalent at level zero.
- The derived level-one relation on the actual glued node set is universal.

Thus the private-to-core transition is a concrete theorem about the
generated quotient, not a proposed contact assignment.

## Validation and provenance

The final module compilation and regression check exit successfully.
The existing strict checker validates the transitive axiom dependencies of
50 declarations: 40 module definitions/theorems and 10 regression
declarations (two definitions and eight theorems). Its output is:

```text
Checked 50 declarations; only the standard logical axioms occur.
```

Only `propext`, `Classical.choice`, and `Quot.sound` occur. The check rejects
missing or unexpected declaration results as well as `sorryAx`, custom
axioms, and native-decision axioms.

Commands from the isolated checkout:

```bash
source /workspace/scratch/095f642caf71/runtime/env.sh
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lake env lean -o .lake/build/lib/lean/Girth/ACopyLayeredStar.olean Girth/ACopyLayeredStar.lean
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lake env lean CheckACopyLayeredStar.lean
python scripts/check_axioms.py checks/a-copy-applications-20261109/layered-axioms.log CheckACopyLayeredStar.lean
```

Lean is 4.35.0-rc3 with `LEAN_NUM_THREADS=1`, scheduled through the shared
two-slot wrapper. The only final diagnostic is Lake's pre-existing warning
that the runtime-patched `batteries` repository has local changes. There
are no final Lean declaration warnings or errors.

The new module imports only `Girth.ACopyExactStar`. Source writes are
limited to `Girth/ACopyLayeredStar.lean`, `CheckACopyLayeredStar.lean`, and
the `layered-*` validation files in this directory. Its compiled `.olean`
is local under `.lake/build/lib/lean/Girth`. No existing module, dependency,
runtime file, Lake configuration, Git state, other checkout, or TeX source
was edited. `layered-validation.json` records exact file hashes and audits.
