# Track 7 — one more quantifier in cutoff-two rank induction

**15 November 2026; additive, source-audited draft; no new Lean kernel run.**

## Exact current representation

The existing checked source
`Girth/TrainFillingColouredOrderedEdgePresentation.lean` defines

    colouredOrderedEdgeLanguage (I : Type u) (k : ℕ)

with a k-ary relation for a full hyperedge, unary colour predicates
indexed by I, and a binary order relation within each colour. The
canonical ordered one-edge source is
`colouredOrderedEdgeSource k sourceColour`.

The cutoff-two construction first obtains an EHN Ramsey **hypergraph**
X for the disjoint union W of the old first wagons. It then creates
a SHORTER train M whose NEW FULL HYPEREDGES are on the ordered
vertex set V(X), not the individual smaller edges of X.

Consequently the new train's edge **type** is the ordered
COLOURED ONE-EDGE structure on V(X). Its arity is

    k_new = |V(X)|,

not the original edge arity k_old, and not `|E(X)|`.
The palette in the recursive tail call has cardinality

    r ^ |E(X)|,

because one short-train colour records an r-colour for every
SMALL original hyperedge of X. These are two different counts.

## Why the earlier all-input wrapper is not yet enough

The draft `UniformSelectedPartiteForestAllInputs L t` in PR #1073
quantifies over every finite ordered source A and palette, but
keeps ONE fixed relational language L. With the current
k-ary edge presentation, the formal language depends on k.
Thus a fixed-L recursive assertion cannot directly be used
at a different edge size without a separate language-transfer
theorem. No such theorem has been established.

The new `UniformSelectedPartiteForestEveryColouredArity` quantifies
over every finite ordered colour-index type I, every genuine arity k≥2, every
finite ordered A-structure in `colouredOrderedEdgeLanguage I k`,
and every finite nonempty palette, BEFORE the cutoff-vector
well-founded induction.

The lemma
`uniformSelectedPartiteForestEveryColouredArity_largerCutoff`
lifts the already kernel-checked q>2 conditional forest proof
POINTWISE over those choices. It does not change its physical
geometry, witness family, rank decrease or selected arrow.

`uniformEveryColouredArityOperators` gives the actual proved
larger-cutoff field, with three visible remaining premises:
baseTwo, same-vector forest-to-UNRESTRICTED-order and cutoffTwo.
No partite-order output is substituted for nonpartite RR_tail.
The latter must also quantify over changing edge arity and
palette before it may legitimately feed cutoff-two.

## Other independent correctness checks

This additional arity issue is separate from:

1. The lack of a global **fine X-part map** on the shorter train
   when two different X-coordinates are identified at a shared
   old vertex (formal obstruction in draft PR #1073).
2. The impossibility of using only identity B→B projections
   for a multi-copy target (formal obstruction also in #1073).
3. The weakness of merely requiring pullback allowedB-parameters
   on prescribed B-images of a large D-base without covering
   the permitted D-points (counterexample/preparation draft
   PR #1075).

Any complete nonpartite RR assertion used at cutoff-two must
address all three and the actual changing k.

## Integration with current mainline (16 November)

The earlier branch was based on the 15 November mainline and
had a checker-script conflict after the latest Track 1 integration.
A two-parent merge commit `424ddc7787680b1a89de288babad2a22e9ffaeb3`
now retains the latest merged mainline tree and adds only these four
new artifacts plus one `CheckTrainRecursiveUniformLanguages`
registration. The PR diff was independently checked: five files
only, with no duplicate or replaced existing source files.

The actual theorem specialization `atColourWord` now introduces its
nonempty finite function palette **both at theorem statement
elaboration and inside the proof**. Without the first binder the
declared `UniformSelectedPartiteForest` type cannot be elaborated.

The finite colour palette `Fin n → Fin r` needs `r>0` but does
not require `n>0`. The coloured edge arity requires `k≥2`.
A genuine source-edge-type specialization to the canonical
`colouredOrderedEdgeSource k sourceColour` is a possible future
refinement: the present proposition still quantifies over *all*
finite ordered structures in `colouredOrderedEdgeLanguage I k`,
so the full base-two operator is stronger than the final
one-edge-source application. This does not affect the validity of
the conditional q>2 pointwise transition.

## Exact verification boundary

This branch changes no existing verified proof or manuscript marker.
The new source and standalone checker have been statically audited
(no sorry/admit/new axioms, balanced syntax). However **no Lean
elaboration or #print axioms output** has yet been obtained. Exact
local check:

    bash scripts/check_track7_languages_local.sh

The four new public statements are conditional logical
uniformization/assembly, NOT existence of base [2], cutoff-two,
unrestricted same-vector RR, or the final theorem.
