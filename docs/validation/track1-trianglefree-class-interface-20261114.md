# Track 1: triangle-free EHN class — minimal Lean interface

**Status 14 November 2026:** source and finite-audit validated only;
new Lean module **uncompiled**, `#print axioms` not executed.
Merged manuscript `girth/main@61b5a511ceb7bf4bb483ccdcf564306af23b7dc6`.

## Simplified mathematical proof

For a relational free amalgam of two `A`-linear and
`A`-girth>3 sides over an `A`-strong induced overlap,
`A`-linearity of the union is **already proved** by
`Girth/ElementaryClosureAmalgam.lean`:
`aLinear_of_freeAmalgam`. To rule out a Berge triangle,
let three support edges be its members. Two lie on one side.
The third meets the overlap in its two **distinct** connectors,
and `A`-strongness puts that third support edge into the
overlap, hence into the first side. The contradiction is
the first side's girth>3. This avoids maximal private-edge runs.

## New exact conditional result

`Girth/Track1StrongOverlapGirthThree.lean` contains draft
`girthGT_three_union_of_strong_overlap`, assuming:

- `GirthGT HL 3`, `GirthGT HR 3`;
- `GirthGT (HL ∪ HR) 2` (global linearity);
- every left/right edge intersection lies in the overlap carrier `S`;
- if a right edge meets `S` twice, the same physical edge belongs
  to `HL`, and symmetrically for left edges.

Its proof examines all 8 possible left/right assignments of a
3-edge Berge cycle and reduces each mixed case by one
strong-overlap reflection to a pure-side cycle.
The checker `CheckTrack1StrongOverlapGirthThree.lean` is
present but **has not been run**. No kernel claim.

## Deriving actual premises from existing modules

Given a functional free amalgam
`StructuralRamsey.Structure.IsFreeAmalgam sL sR iL iR`
and `ElementaryCAClass A` on each side:

1. `closureFreeAmalgamRel` gives the relational free diagram.
2. `closureEmbedding_range_aStrong` on `sL,sR` gives
   `A`-strongness of the shared domain in each side.
3. `irreducibleCopy_side_of_freeAmalgam` in the existing
   `ElementaryClosureAmalgam` geometry places each physical
   `A`-copy in one side. Prove its support hypergraph equals
   the union of the two mapped side support hypergraphs.
4. The free-amalgam `overlap` axiom gives the cross-contact
   restriction `eLeft ∩ eRight ⊆ S`.
5. If a right `A`-copy meets `S` twice, the source
   `A`-strongness forces its whole carrier into the common
   induced domain. Its image is then also an `A`-copy
   in the left side. This is exactly the reflection premise;
   similarly from left to right.
6. `aLinear_of_freeAmalgam` plus
   `girthGT_two_of_aLinear` gives the global two-cycle bound;
   apply the new strong-overlap theorem and transport along
   the support-union equality.
7. Define the restricted class
   `C ↦ ElementaryCAClass A C ∧
       GirthGT (supportCopies A (closureRelReduct C)) 3`.
   Heredity follows from `girthGT_of_subset` and
   `girthGT_source_of_mappedSupportCopies` in
   `Girth/SupportGirthEmbeddingEquiv.lean`. Free amalgamation
   follows from steps 1–6 and the existing
   `ElementaryCAClass_freeAmalgamationClass`.
   Finally apply functional `orderedRamsey_of_mem_target`
   and retain the selected full ordered target embeddings.

## Bounded adversarial test

An independently executed exhaustive test checked **408,749**
free amalgams of two possibly different linear triangle-free
small uniform supports over induced strong overlaps:

- 402,362 graph amalgams (397,050 from different sources);
- 6,387 three-uniform amalgams (5,960 different sources).

Every output remained linear and triangle-free, and both
constituents remained strong. A negative test with **no strong
closure** glued `{0,1,2}` and `{0,1,3}` along `{0,1}`,
creating a Berge two-cycle. The distinction demonstrates why
ordinary induced overlaps do not suffice.

The finite result is a **regression diagnostic**, not a proof
or a Lean certificate. No TeX or GitHub Actions build was run.

## Validation gate

Before marking `obs:functionalinput` or
`thm:AlinearRamsey` verified: compile the new generic theorem
and full functional-class adapter on the pinned Lean head; run
`#print axioms` and check for unexpected axioms or
`sorryAx`; confirm the selected family retains the fresh
order and that the unmarked target expansion belongs to the
triangle-free class. The external EHN input remains explicit.

## 14 November follow-up — concrete draft adapters

Additional source files now exist on this branch:

- `Girth/Track1FreeAmalgamSupport.lean`: exact equality of the whole
  A-support with the two mapped constituent support families, and
  the cross-side intersection-in-base property, reusing
  `irreducibleCopy_side_of_freeAmalgam` and
  `freeAmalgam_side_intersection`.
- `Girth/Track1StrongAmalgamGirthThree.lean`: factor a right A-copy
  meeting the common base twice into the left constituent by the
  **already proved** `freeAmalgam_left_aStrong`; the converse uses
  `freeAmalgam_right_aStrong`. Combining those reflections, the
  support-union equality, existing A-linearity, and the three-edge
  lemma yields the exact relational statement:
  `track1_girthGT_three_freeAmalgam_of_aStrong`.
- `Girth/Track1TriangleFreeEHNClass.lean`: define
  `ElementaryCAThreeClass` by the original canonical pair closure,
  A-linearity, and support girth>3. Heredity uses the checked support
  embedding/girth transfer; amalgamation uses the relational theorem.
  `c_B` is still arbitrary, so no second closure language or
  extra unary function is introduced.
- `Girth/Track1TriangleFreeSelectedFamily.lean`: specialize the
  earlier `Track1OrderedSelectedFamily` argument to this restricted
  class, retaining the actual full **fresh-order-respecting** B-target
  embeddings, their strongness, controlled intersections, and a
  selected Ramsey arrow. The witness's A-support girth is also >3.

All four are **UNCOMPILED candidates** and their axiom-checker
files have not been executed. Their conclusions are exact interfaces,
not newly verified results. They make the remaining proof-decomposition
clear: the analytical girth>3 restriction is separate from the
owner-splitting coloured witness and cutoff-three partite fusion.

The finite negative control omitting A-strong closure is part of
[the merged distinct-source diagnostic](https://github.com/janhubicka/girth/pull/456).
The author will manually compile the TeX manuscript; none of these
Lean files changes the source or promotes validation markers.
