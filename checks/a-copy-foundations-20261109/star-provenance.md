# Exact star: generated equivalence and source quotients

Validated locally on 2026-11-09 in
`/workspace/scratch/095f642caf71/lean-girth-a-copy`.

## Formalized statement

`Girth/ACopyExactStar.lean` formalizes the abstract quotient assertion in
`paper/11-amalgamation.tex`, Lemma `lem:layeredstarcolimit` (Exact star
realization). The source and shared types may depend on the copy index.
No finiteness or nonemptiness assumption is needed.

The `SourceStar` input consists of a core setoid, an indexed family of
source setoids, and maps `alpha i : Shared i → Core` and
`beta i : Shared i → Source i`. The only compatibility hypothesis is

```lean
∀ i s t,
  coreEq (alpha i s) (alpha i t) ↔ sourceEq i (beta i s) (beta i t)
```

The manuscript additionally assumes injectivity of the shared maps.
The abstract quotient statement proved here does not need that extra
assumption, so it applies in particular to the manuscript's embeddings.

The raw union is `Core ⊕ Sigma Source`. `SourceStar.Step` contains precisely
the core source relation, each indexed source relation, and each literal
shared pair `beta i s ~ alpha i s`. `SourceStar.Generated` is
`Relation.EqvGen` of that relation. It is not defined as equality of tags.

The constructed partial contact map has domain exactly the source classes
containing a shared representative. Compatibility proves its well-definedness
and partial injectivity. The intermediate `ClassStar.Step` contains precisely
the corresponding source-class-to-core-class contact pairs.

There are two substantive reverse-direction arguments:

1. Each class-level raw node has a generated path to its normal form;
   equal normal forms therefore give an actual equivalence-closure path.
2. A quotient-lift map from the source class union into the quotient of
   original source elements proves that class-level generation creates
   exactly the identifications already generated at the source level.

Thus the proof does not import or assume an equality-of-tags normal form.

## Exact exports

All names below have prefix `StructuralRamsey.Girth.ACopyExactStar.`.

| Export | Proven content |
|---|---|
| `SourceStar.touch_unique`, `touch_injective` | Shared equivalence compatibility gives a partial injection between source and core quotient classes. |
| `SourceStar.contact_eq_some_iff`, `contact_eq_none_iff` | Contact is exactly existence of a shared representative in the source class; absence is the private-class condition. |
| `SourceStar.generated_iff_class_generated` | Generating after quotienting sources agrees exactly with generating source relations and shared pairs together. |
| `SourceStar.generated_iff_normal` | Original-source generated equivalence is equivalent to equality of the constructed core/private normal forms. |
| `SourceStar.generated_core_iff`, `generated_source_iff` | Exact restriction of the generated equivalence to the core and each source. |
| `SourceStar.core_classMap_injective`, `source_classMap_injective` | The maps from every source quotient into the generated quotient are injective. |
| `SourceStar.generated_source_core_iff` | A source element meets a core element exactly through a shared representative, up to their original equivalences. |
| `SourceStar.generated_distinct_sources_iff` | Two different source copies are equivalent exactly when both meet a common original core representative. |
| `SourceStar.quotientEquiv` | A bijection from the genuine generated quotient of the original source union to the active normal-form labels. |
| `ClassStar.normal_range_iff`, `SourceStar.private_label_range_iff` | The active labels are all core classes and exactly private indexed source classes containing no shared representative. |

The quotient-equivalence codomain is implemented as the subtype
`Set.range (ClassStar.normal contact)` inside the tagged union. The two
range theorems identify this subtype exactly with the manuscript's
displayed core union private-class set. Inactive private tags are excluded.

`ClassStar` also exports the corresponding generated-normal-form theorem,
restrictions, cross-source criterion, and quotient equivalence for a supplied
partial contact map. Only its same-source restriction requires partial
injectivity; its generated normal form holds for arbitrary partial contacts.

## Deliberate remaining scope

This module proves the entire abstract setoid quotient lemma, including its
source-level bridge. It does not yet instantiate the theorem with both
point occurrences and physical wagon classes in the recursive construction.
Those applications must identify their actual source setoids and shared
maps, prove the displayed equivalence compatibility, and connect their
generated relations to `SourceStar.Step`.

Active-subsystem coverage, retained chart-point records, induced relational
gluing, parent-map commutation across train levels, and the physical carrier
identifications remain application obligations. The module does not prove
physical linearity, strongness, parameters, or system-girth preservation.
Accordingly, the manuscript's combined marker requesting both the generic
lemma and its simultaneous applications should not be upgraded wholesale
on the strength of this file alone.

No existing Girth theorem is imported. The module imports only
`Mathlib.Logic.Relation`, `Mathlib.Data.Quot`, and `Mathlib.Tactic`.
No public import aggregator or manuscript marker was changed.

## Regression and strict axiom validation

`CheckACopyExactStar.lean` uses parity equivalence on natural numbers,
two source copies, and one shared representative per copy. The shared
source representative is `0`; the shared core representative is `1`.
It proves all of the following:

- Source `2` is generated-equivalent to core `3`, using original source
  and core equivalences around the shared identification.
- Source `2` in the first copy is generated-equivalent to source `4` in
  the other copy through the shared core class.
- The even and odd classes within a source remain different.
- The private odd classes from different sources remain different.

These examples use nontrivial original equivalence classes, rather than
only equality setoids or preassigned tag equalities.

The final module build and check exit successfully. The check prints
transitive axiom dependencies for 32 module declarations and five regression
theorems. The existing `scripts/check_axioms.py` requires exactly the requested
declarations and rejects every axiom outside `propext`, `Classical.choice`,
and `Quot.sound`. Its final output is recorded in `star-strict-audit.log`.
No `sorryAx`, custom axiom, or native-decision axiom is allowed.

Commands, run from the isolated checkout:

```bash
source /workspace/scratch/095f642caf71/runtime/env.sh
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lake env lean -o .lake/build/lib/lean/Girth/ACopyExactStar.olean Girth/ACopyExactStar.lean
/workspace/scratch/095f642caf71/runtime/with-lean-slot.sh lake env lean CheckACopyExactStar.lean
python scripts/check_axioms.py checks/a-copy-foundations-20261109/star-axioms.log CheckACopyExactStar.lean
```

The runtime is Lean 4.35.0-rc3, with `LEAN_NUM_THREADS=1` and the shared
two-slot scheduling wrapper. The isolated dependency directory was prepared
before validation. Mathlib is pinned by the local manifest to
`5bd58ac291422a21f412ae354c91e7d172255a2c`. Lake emits the pre-existing
`batteries: repository has local changes` warning caused by the runtime
compatibility setup; there are no final Lean declaration warnings or errors.

The only source/check/note writes for this task are the new module,
new check, and files prefixed `star-` in this check directory. The module's
compiled output is local under `.lake/build/lib/lean/Girth`. No existing
source module, Lake configuration, dependency source, Git state, or other
checkout was edited. `star-validation.json` records hashes and audit counts.
