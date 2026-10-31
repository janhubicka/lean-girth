# Track B: appended refinement and actual remaining-fibre readiness

Starting point: main `c60b2fa77b8ed35a3b34e4caeed027c9ab94b6f8`, including
Track B PR #715 and the concurrently merged A/C/D additions. These additions
are preserved; the proof code here extends the unchanged Track B base.
Scope: the circulation proof; no appendix changes.

The previous pass constructed the literal next stage and identified the
complete untouched physical support with standard-index/old-edge pairs.
This pass constructs every field of the appended first-wagon refinement
and uses it to preserve the actual remaining-fibre invariant.

## The complete appended partitions

Write `d = R.extraCuts + 1` for the old refinement depth. On physical edge
pairs `(i, a)`, the lower cuts through `d` require the same standard index
and the corresponding old refined relation. Above these cuts, the relation
is the actual output train relation at the index shifted down by `d`.
The physical bottom remains cut zero. Each positive output cut `mu` is
retained at `mu + d`; this statement is about the output train, whose
first wagons may join several standards.

Exact first-cut restriction inside a standard supplies both directions
needed by this construction. Preservation gives nesting at the join;
reflection proves that two children with the same standard owner and
the same new parent are equal. The resulting owner map is injective
within each fixed new parent. No global owner injection is assumed.

At every inherited cut, the full quotient labels are equivalent to pairs
of a standard index and an old quotient label. The carrier is the entire
standard image of the old wagon carrier, and the actual parent square
commutes. These identities transport the inherited allowed-part bounds
and labelled child girth, without identifying equal carriers.

## The new level and its permitted part

The new child family of a fixed first parent has distinct standard owners.
Its carriers lie in the true untouched active systems of those standards.
Cross-standard intersections are confined to the intersection of the
processed and untouched base carriers, which is a subsingleton by base
A-linearity. The new permitted set is this common part intersected with
the output first allowed set.

The first-allowed-set clause is derived from the output adjacent parameter:
choose physical edges witnessing the common vertex in the two distinct
children. Their standard owners differ, so the physical edge labels differ.
They have the same output first parent, and the bottom-to-first parameter
applies. The proof does not mistake distinct child labels for distinct
vertex carriers.

The earlier local forest theorem now applies to the complete quotient
child family, using the owner injection and containment proved here.
Only the used standard indices through the required cutoff are needed.
The optional finite mixed-forest wrapper retains the explicit injection
of the physical gluing pieces.

## Return to actual physical support

The constructed product refinement is transported through the previously
proved physical-edge equivalence to the complete new untouched support.
The transport theorem preserves full wagon labels, actual parent maps,
carrier images, permitted parts and every labelled child-girth field.

The actual constructor retains the necessary hypothesis that every core
vertex projects into the processed base copy. Core partiteness alone
does not imply this support restriction. No completed output refinement,
chosen support subfamily or supplied child-owner injection is required.

## Remaining profiles and the selected step

The actual stage constructor already supplies every output adjacent
parameter used above. Its existing local-forest alternative also supplies
the predecessor cutoff: at bottom cutoff two, the required cutoff is one,
where the one-member forest theorem applies automatically.

For each remaining profile, either it is the projection of a genuine base
embedding, in which case the untouched refinement constructor applies,
or its active carrier is empty by output partiteness. In the latter case
all physical support carriers are empty and there is at most one physical
edge label, so the matching refinement is constructed directly. This
argument includes an empty source and assumes no source nonemptiness.

The selected picture-step theorem pairs this actual readiness result with
the ordinary local Ramsey family arrow. Freshness excludes the processed
profile from the remaining list. The finite-pass facade derives freshness
from the repetition-free list of projection profiles and carries its
`Nodup` invariant through both identity and nontrivial steps. It does not
ask for readiness of a processed fibre after its own attachment.

## Remaining boundary and validation

Genuine nontrivial local witness existence and the indexed positive-cut
supreme-cycle transfer remain separate construction obligations. The
core-support hypothesis must also be met by that witness construction.
The new finite pass is conditional on those actual nontrivial steps;
no unconditional forest Ramsey theorem is claimed.

Every public definition and theorem in the six new modules has an explicit
`#print axioms` check. The focused workflow builds from fresh project proof
objects, audits all declared exports, runs its established finite geometry
and boundary regressions, and retains the logs. Complete exact-head focused
and repository-wide CI, including artifact, cache and post-job steps, are
required before merge and before manuscript links are marked verified.
