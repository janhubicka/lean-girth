# Track B: recursive active inputs, coarse parameters and empty sources

Scope: the circulation proof; no appendix changes. This continuation extends
the actual stage and appended-refinement interfaces already constructed in
PR #729. It does not reopen readiness as an unproved construction or claim
the final Ramsey theorem.

The three modules add 13 explicitly audited exports: nine theorems and four
definitions. Local compilation and all 13 repository axiom checks have
passed. The proposed publication still requires complete focused and full
repository CI; those results are not asserted here in advance.

## The true active source and the local partite arrow

`TrainRecursiveActivePartite` reuses `actualActiveSubsystemPartite` from
`ActualActivePartitePresentation`. Its vertices are exactly the true active
carrier, and its induced relations are unchanged. Only the part labels are
pulled back through the processed base embedding. The construction never
replaces the active carrier by all vertices in the same ambient parts.

`actualActiveSubsystemPartite_isPartiteOver` supplies the full
`IsPartiteOver` property over the source A, including the required
reflection on irreducible substructures. Its input is the corresponding
partite property of the old picture over the base and an actual embedding
of A into that base. The proof factors the true active subsystem through
the existing restricted partite picture; it does not introduce a second
active-source construction.

For an A-partite local core E and a family of partite embeddings from that
source, `activePartiteToRelabelledCore` gives the literal attachment maps
into the core relabelled by the processed embedding. The underlying
relational embeddings remain the same. The projected-copy conversions
`activeProjectedPartite` and `partiteEmbedding_relabelProjected` make the
two routes for each projected A-copy equal as actual embeddings.

Consequently, `activeLocalSelection_of_partiteFamilyArrow` needs only the
Ramsey family arrow for part-preserving copies of the transversal A in E.
It pulls a colouring back along the projected-copy conversion. There is no
extension of the colouring to unrelated relational A-embeddings, and no
`Nonempty κ` premise is needed for this selection theorem or its actual
refining-picture-step wrapper.

Every relabelled core vertex y projects to the image of `E.part y` under
the processed embedding. Thus the whole-core support condition required
by the PR #729 readiness constructor is proved automatically. The wrapper
returns both the actual next stage's remaining-fibre readiness and its
literal `PictureStep`.

This simplification does not manufacture the local witness. The finite
core and family, actual active projected copy, base A-linearity, positive
train height, fresh profile and old readiness remain inputs. The full
`ActiveAttachmentBounds` record remains explicit, including core
partiteness and coverage, the prescribed strong base copies, interior
train compatibility, local forest/girth data, core parameters and indexed
output supreme-cycle transfer. No bound field is silently discharged by
the weaker family arrow.

## Recovering every coarse adjacent parameter

`TrainRecursiveRefinementParameters` fills a different interface gap.
After inserted first cuts are forgotten, the physical equality cut is
followed by fine cut `d + 1`. Those cuts were not adjacent in the fine
train, so a direct adjacent-cut transport is insufficient at the bottom.

`edgeIntersection_of_firstCommonAncestor` descends from a common fine
parent of two distinct physical edges. At the first level where their
children differ, the actual adjacent sibling parameter bounds their
intersection. Containment of the positive fine permitted sets below that
parent in a chosen allowed set gives the desired physical-edge bound.
The equality bottom rules out continuing the descent past cut zero.

`forgetFirstCuts_adjacentParameters` applies this argument to the new
bottom-to-first parameter. Every positive fine permitted set through
`d + 1` must lie inside the original first permitted set. For positive
coarse cuts, the common index shift preserves adjacency; the existing
quotient equivalences identify the full wagon labels, their carriers and
their actual parent maps. The retained fine permitted sets need only be
subsets of the corresponding coarse allowed sets.

The result proves all coarse adjacent parameters from fine parameters and
these containments. It assumes positive coarse height, but assumes no
coarse parameter, child-girth bound, or singleton permitted set. Physical
edges are retained, and equal vertex carriers do not identify labels.
The recursive construction must still supply the fine parameter data and
the stated permitted-set containments.

## The actual empty-source stage

`TrainRecursiveEmptySource` treats the case that the disjoint-initial-stage
argument could not handle by recovering component labels from a source
vertex. If A has no vertices and the target satisfies `hSupportCovers`,
then every target vertex would belong to the image of an empty A-copy.
Hence the target vertex type is empty as well.

`emptySourceOrderStage` constructs an actual complete stage in this case.
Its system is the target B itself, projected through a supplied member of
the prescribed base family. Its selected copy is the literal identity
B-copy, and its train is exactly the supplied target train. The required
nonempty physical support is retained: the empty support edge is not
deleted or replaced by a support subfamily.

Empty vertices and the resulting subsingleton wagon-label types preclude
a genuine cycle with two distinct connectors. This supplies full
simultaneous system girth at every cut and cutoff, together with all
forest and stage fields. The selected arrow follows because embeddings
with empty domain agree. The direct stage and its arrow require neither
an admissibility or girth input nor `Nonempty κ`; they do retain support
nonemptiness, support coverage and a genuine base-family member.

`constructFromTargetCuts_of_freshNontrivialRefiningSteps_allowEmpty`
splits the source into the empty and nonempty cases. The nonempty branch
reuses the existing repetition-free finite pass. The empty branch uses
the constructed stage above and obtains the required base-family member
from the original base arrow.

This facade removes `Nonempty UA` from its hypotheses under
`hSupportCovers`. Its common signature still includes `Nonempty κ`, the
base arrow, admissible target cuts, target support and parameter/girth
data, and the actual fresh nontrivial refining-step operator. Those
inputs serve the nonempty branch; no unconditional recursive witness
existence or general cycle-transfer result is claimed.

## Hypothesis ledger and verification boundary

| Previous obligation | Result in this continuation | Inputs still supplied |
|---|---|---|
| Genuine A-partite active source | Reuse the canonical true active subsystem and prove its full partite property | Old picture partiteness and the actual processed base embedding |
| Stronger arrow on all relational core embeddings and separate core support | A partite family arrow gives exact projected selection; relabelling gives whole-core support | Finite local witness and all other `ActiveAttachmentBounds` |
| Coarse adjacent parameters after forgetting first cuts | Derive every coarse parameter from the fine train | Fine adjacent parameters and permitted-set containments |
| Source nonemptiness in the target-cut facade | Construct the actual empty-source stage and split the cases | Covered target, support/base-arrow hypotheses and the nonempty branch's fresh local-step operator |

Each public export has an explicit `#print axioms` check. The focused
workflow now includes 42 module/Check pairs and 184 audited exports,
retaining the existing six finite regressions, exact-head checkout,
fresh project build, artifact upload and cache/post-job gates. Complete
focused, repository-wide and applicable Track D CI must finish before
merge or verified manuscript annotations. The outstanding mathematical
work is to instantiate the genuine nontrivial recursive local witnesses
and the remaining indexed positive-cut supreme-cycle construction at
their actual scopes, not to rebuild the readiness already proved.
