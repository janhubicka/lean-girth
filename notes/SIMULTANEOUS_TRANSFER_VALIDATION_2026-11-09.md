# Simultaneous-transfer source-correspondence audit — 9 November 2026

This report concerns the circulation simplification on the separate
`girth` branch `audit/circulation-independent-referees-20261109`, starting at
`bce381293fd63dbd773171157c2c195054b04e03`, and local Lean validation branch
`validation/simultaneous-transfer-20261109`, based on
`0a5bf1f11c1411003f8933701aad54e77f41c128`. Neither main nor the ongoing
validation branches are changed by this audit.

## Final local validation result

**Passed.** The central gate finished with exit status zero at
`2026-11-09T08:59:26.387824+00:00`. It built these exact targets and their
dependencies with the repository-pinned Lean `4.35.0-rc3`, compiler
commit `470d5ce1400764999581fd26d5d72b00d990b0f4`:

- `Girth.TrainActualCirculationCycleTransfer`
- `Girth.TrainEndpointGeometry`
- `Girth.UntouchedGirthTransversalBridge`

All seven root check files elaborated and passed the strict axiom
checker: **68 export checks covering 60 distinct declarations**. Only
`propext`, `Classical.choice`, and `Quot.sound` occurred in their
transitive axiom closures. SHA256 snapshots covered **420 local Lean
source/check files**; the end-of-run check confirmed no source drift.

| Root check | Exact exports checked |
| --- | ---: |
| `CheckSimultaneousSegmentClassification.lean` | 21 |
| `CheckActualSimultaneousSegmentTransfer.lean` | 8 |
| `CheckActualOriginalTwoCycleSupreme.lean` | 5 |
| `CheckTwoCutGeometricSupreme.lean` | 3 |
| `CheckActualBottomReducedTransfer.lean` | 10 |
| `CheckActualCirculationCycleTransfer.lean` | 1 |
| `CheckSimplifiedCirculationInterfaces.lean` | 20 |

The result manifest is `local-validation/simultaneous/result.json`,
SHA256 `f8cd5593cb7ef6cd010947410208d54f601fbc1824e35ac809ad29b8903404bf`.
It records the base Git HEAD and exact hashes of the checked branch
sources, so uncommitted additions at the time of testing are not hidden
behind the base SHA. Individual build, Lean and axiom-check logs are in
the same directory. Reproduce with
`bash scripts/validate_simultaneous_transfer.sh` after restoring the
pinned toolchain and dependencies. Runtime provenance and the narrowly
scoped container compatibility shim are documented in
`notes/LOCAL_LEAN_RUNTIME_2026-11-09.md`.

This was a focused dependency-closure validation, not a build of every
module in the whole repository or a certificate for the entire recursive
witness construction.

## Findings from independent source inspection

The principal simplification is already represented by a precise Lean
proof in the base revision. `TrainActualThreeCutOnePassSupreme.lean`
chooses **one** globally legal reduced supreme plan, expands that same
plan occurrence by occurrence on the original cycle, and transfers the
old bound once. It does not use an owner-cut or designated-count descent.
The local revalidation compiled this proof and its dependency closure
and inspected its axiom closure. The branch also closes the original
length-two case and supplies the weaker bottom-transfer interface;
these are substantive additions beyond renaming the existing theorem.

| Proposed passage | Exact Lean interface | Correspondence and scope |
| --- | --- | --- |
| `paper/05-local-tree-construction.tex`, untouched fibre | `strongSupportPieces_meet_baseFinePartAtMostOne`; `no_short_untouched_cycle_of_transversal_local_support` | Transversality bounds **support edges**, not entire gluing carriers. The corrected conclusion is already proved by an incidence-forest argument. The new leaf-separator derivation is not literally formalized here. |
| No owner cuts | `attachedSelectedPicture_zero_cut_supreme_of_old_bound` | Full original `HasSimultaneousSupreme`, with literal original label/connector identities, complete legal plan transport and equal twice-order. |
| At least three cuts, a specified reduced supreme plan | `attachedSelectedPicture_three_cut_one_pass_supreme_of_old_bound` | Exact simultaneous proof route: one fixed plan; singleton short/fresh-long cases; two shorts retaining an old internal wagon; globally legal source replacement. |
| Obtain that plan from the witness bound | `attachedSelectedPicture_three_cut_reduced_supreme_of_fullSystem`; `attachedSelectedPicture_three_cut_full_supreme_of_old_and_witness` | The actual cut reduct is acceptable above order one. The witness's genuine bound provides a supreme designated standard. |
| Exactly two cuts, source length at least three | `attachedSelectedPicture_two_cut_two_standards_full_supreme`; `attachedSelectedPicture_two_cut_three_le_full_supreme` | Pair-edge, no-pair long, mixed bridge, and impossible wagon/wagon cases are present. The second theorem also covers standard/core labels; it does not cover original source length two. |
| Assemble all owner-count cases | `attachedSelectedPicture_fullSystemGirth_of_two_cut_cases` | A complete output-bound theorem **conditional on** the exact-two-cut callback. It chooses a minimal owner assignment but does not use minimality. |
| Reduce the last callback to source length two | `attachedSelectedPicture_fullSystemGirth_of_length_two_two_cut` | Combines the preceding interfaces; the original `BigCycle 2` callback is an explicit remaining premise at the base revision. |

The branch's fixed-plan segment audit is in
`CheckSimultaneousSegmentClassification.lean`. The interface-level audit
is in the root file `CheckSimplifiedCirculationInterfaces.lean`.

The new `TrainActualSimultaneousSegmentTransfer.lean` exposes
the same argument as an explicit certificate. Its
`attachedSelectedPicture_expanded_plan_keep_iff_target_owner` records
that **all** occurrences of the chosen owner are retained, including
separated runs. The fixed-plan certificate adds physical local
incidence, long-piece geometry, freshness against every source connector,
and containment of every entry of the literal result word in that
standard. Its direct transfer endpoint uses one witness plan and one
application of standard-contained replacement. Independent source
inspection found no extra hidden assumption or plan reselection. This
presentation compiled and passed its dedicated
`CheckActualSimultaneousSegmentTransfer.lean` audit.

## Actual hypotheses retained by the formal interface

The proofs are conditional on genuine actual attachment geometry, not
arbitrary sets labelled as standards. In particular they retain:

- finite irreducible `A`, the actual active carrier, and actual
  `OldACarrierEdge` support;
- strongness of the base designated copies and at least two distinct
  support edges in each selected target; the manuscript explicitly
  separates its one-edge target case before this section;
- `AStrong` for the entire old active subsystem and for every complete
  core gluing image, not just each individual edge;
- a nonempty shared support for every gluing copy and equality in both
  directions of all shared train relations at every level;
- real geometric owner incidence, output pretrain linearity where used,
  source acceptability, and the source twice-order budget;
- the old standard `SupremeCycleBound q`; aggregate theorems also use
  the genuine witness `FullSystemGirthGT q`.

These are the conditions supplied or claimed by the surrounding picture
construction. This audit does not certify the entire recursive witness
construction merely because the local conditional implication compiles.

## Scope issue found and resolved

The initially proposed `lem:cycletransfer` allowed a chosen reduct already known to be
supreme, or an order-one reduct with bridges, and assumed only witness
girth greater than two for nonsingleton wagons. For singleton-edge
wagons it gave an additional argument obtaining both mixed bridges
without a separate full witness bound.

The three-cut one-pass theorem accepts the specified reduced supreme
plan directly and closely matches this weaker local formulation.
The existing two-cut aggregate and full-output interfaces instead assume
`FullSystemGirthGT q` throughout the whole required cutoff. Therefore
their successful validation proves the conditional implication needed
by `thm:preservation` (where the witness does have the full bound), but
does not by itself certify every weakening in the standalone lemma,
especially the singleton-wagon alternative. This is a difference of
formal scope, not a counterexample to the manuscript argument.

The weaker singleton-wagon alternative is needed elsewhere: the two
applications in `paper/14-conversion.tex` (the proof of
`lem:squareclean`) start only with a local forest through size `q`.
They do not have a witness `FullSystemGirthGT q`; producing the bottom
order bound is the purpose of that conversion. Strengthening the
standalone lemma everywhere to assume a full witness bound would
therefore break these applications or make their argument circular.
The branch consequently retains and now formally proves the bottom
interface with exactly these weaker witness hypotheses. It restricts
the unused nonsingleton weakening as described below.

## Axiom-audit procedure

The repository checker accepts only `propext`, `Classical.choice`, and
`Quot.sound`. Its requested declaration set comes from exact root-level
lines of the form `#print axioms FULL_NAME`; the emitted declaration set
must equal that requested set. A missing declaration, extra declaration,
`sorryAx`, or other extra axiom fails the check. A source-text search is
not a substitute for this transitive kernel audit.

Record both a successful Lean process exit and a successful checker
exit. In shell pipelines enable `pipefail`, since a successful `tee`
or checker alone does not establish successful Lean elaboration.

```sh
set -o pipefail
lake env lean CheckSimplifiedCirculationInterfaces.lean 2>&1 | tee INTERFACES_LOG
python scripts/check_axioms.py INTERFACES_LOG CheckSimplifiedCirculationInterfaces.lean
lake env lean CheckSimultaneousSegmentClassification.lean 2>&1 | tee SEGMENTS_LOG
python scripts/check_axioms.py SEGMENTS_LOG CheckSimultaneousSegmentClassification.lean
```

The custom checks are at repository root because the repository CI loops
over root `Check*.lean`; placing them only under `scripts/` would omit
them from that loop.

## Additional audit evidence

- Read the full exact one-pass, zero-cut, three-cut assembly, two-cut
  dispatch and residual-closure sources, and compared their actual
  hypotheses with the modified English argument.
- A lexical inventory of the combined dependency closure of the
  existing one-pass, zero-cut, two-cut, residual and untouched-fibre
  interfaces contains 369 `Girth` modules. After stripping comments and
  strings, no `sorry`, `sorryAx`, `admit`, `axiom`, `unsafe`,
  `native_decide` or `implemented_by` tokens occur there. This is source
  evidence only, not a compilation or kernel certificate.
- Local installation, dependency builds, original-length-two integration,
  simultaneous-plan checking and bottom-scope checking ran in parallel
  tracks; the final combined gate above rechecked their frozen sources.
- `python -m unittest scripts/test_check_axioms.py` passed all six
  checker regression tests in this checkout. This validates the audit
  harness's tested failure cases; it is not a Lean theorem result.

## Independent review of original length two

The new `TrainActualOriginalTwoCycleSupreme.lean` was read in
full, including the lower-level designated-existence, short-plan,
old-bridge and two-wagon interfaces it invokes. The source matches the
manuscript's original-length-two argument:

1. It first chooses a genuinely designated **original source** occurrence
   from the actual source's acceptability and linearity. It does not
   identify a reduced owner label with that source occurrence.
2. For two vertex connectors, actual core-to-standard preimages and the
   active-boundary dichotomy produce a support edge inside that exact
   original target, containing both vertices. The common-short plan
   retains the original designated occurrence.
3. For mixed connectors, uniqueness of the designated label's geometric
   owner identifies its real standard. The witness bridge in that
   standard is a genuine shared edge. Exact block pullback recovers an
   old wagon with both the original target incidence and that edge
   incidence. `bridge_of_incident_edge` is the old order-one physical
   edge probe; it supplies an edge **inside the original target**. The
   transported edge has the original output wagon as parent. This is
   exactly the retention required by (A1).
4. For two wagon connectors, the actual twice-order is four, so the
   source budget gives `q ≥ 2`. The genuine witness bound excludes the
   two-wagon reduct; no output-girth conclusion is assumed to obtain
   this contradiction.

`TrainActualOutputGirthFromOriginalTwo.lean` now dispatches directly from
an arbitrary admissible geometric owner assignment, chosen separately
at each source occurrence from the actual label-cover theorem. It does
not choose a minimum assignment at this entry point. Zero cuts use the
literal old transport; exactly two cuts split original length two from
longer sources; at least three cuts invoke the new simultaneous-segment
certificate endpoint. Thus its
`attachedSelectedPicture_fullSystemGirth` has no residual source-cycle
or two-cut callback in its hypotheses. Its remaining assumptions are
the geometry, output linearity and ordinary old/witness bounds listed
above. Independent inspection of this updated dispatcher also passed.
Fresh local elaboration and axiom checks passed, formally closing the
residual callback under these geometric assumptions. Older imported
carrier-containment helpers may still select a minimum assignment as
an existence proof; no minimum hypothesis or descent is needed here.

The combined interface check now requests 20 exact declarations,
including the new three-part certificate interface and closed output
endpoint, plus the two bottom endpoints and literal-bottom parent
injectivity described below, and the numerical order-one classification.
The dedicated original-length-two check also audits its
two geometric helper theorems and original-source supremacy theorem.

## Independent review of the weaker bottom transfer

`TrainBottomReducedSupremePieces.lean` expresses singleton-edge wagons
by injectivity of the physical edge's `parent` map. Two different edges
cannot form a long piece in such a wagon. A bridge from one label is a
bridge from every label meeting that wagon, because both use the same
physical edge. At two reduced occurrences, a chosen full supreme plan
therefore supplies one actual edge incident with both connectors and,
in the mixed case, bridges in both labels.

There is also a useful simplification of the order-one bridge alternative:
two physical reduced labels meeting the same bottom wagon would be the
same physical edge, contrary to adjacent-label distinctness. Therefore
explicit bottom bridges force a designated reduced label and yield a
genuine complete short supreme plan. This argument does not assume (A1)
for an otherwise edge-only reduct.

The actual `TrainActualBottomReducedTransfer.lean` dispatches
the resulting plan at every original source length. It uses the
geometric pair-edge transfer for two standard vertex boundaries, the
explicit bridges for mixed boundaries, the chosen reduced plan for a
standard/core pair, and the original-designated target/probe proof at
source length two. At three or more cuts it invokes the same fixed-plan
one-pass theorem. The two final interfaces are
`attachedSelectedPicture_bottom_reduced_supreme` and
`attachedSelectedPicture_bottom_mixed_bridges_supreme`.

Both retain the genuine geometry and old bound while requiring **no
full witness system-girth bound**. Independent source inspection of the
generic and actual modules found no circular premise. These are the
checked interfaces for the two transfer applications in
`paper/14-conversion.tex`; they do not themselves formalize the preceding
minimum-segmentation or local-forest-to-reduct arguments of that lemma.
Literal-bottom parent injectivity is already supplied by
`EdgeTrainLevels.bottom_parent_injective` in
`TrainEndpointGeometry.lean`: quotient equality implies the bottom
relation and the bottom relation is physical edge equality. The parent
map in `sharedWitnessOrderOneData` is definitionally that quotient map,
so the singleton-wagon hypothesis introduces no extra bottom assumption.
This existing endpoint is also requested by the combined axiom check.
Both modules and their transitive dependencies compiled; their dedicated
ten-declaration audit and combined interface audit passed.

The order-one bridge alternative has exactly the type required by the
bottom endpoint. `BigCycle.length_eq_two_of_order_one` proves that a
genuine big cycle with twice-order two has exactly two occurrences;
`BigCycle.connectors_mixed_of_order_one` then proves that its two
connectors have opposite kinds. Applied to the actual cut reduct, this
gives exactly two owner cuts and the vertex/wagon or wagon/vertex pair
at indices zero and one. Neither numerical fact assumes (A1).

## Deliberate manuscript scope simplification

The parent task accepted a minimal restriction of the standalone
`lem:cycletransfer` statement: fix `q ≥ 2`, require the source order and
the actual old-picture bound through `q`, and require witness system
girth greater than `q` when wagons are not singleton edges. The
singleton-wagon reduced-plan/bridge alternative is retained. This
matches the two separately validated interfaces and preserves both
applications: ordinary one-level preservation uses the full witness
bound, whereas the bottom forest-to-order proof uses its selected
reduct and bridges without a full witness bound.

The restriction removes an unused nonsingleton weakening. It is a
deliberate simplification of scope, not a claim that the earlier weaker
English statement was false. No proof step, main theorem or bottom
conversion application is lost. Validation markers must still identify
the exact formal conditional scope and must not certify the whole
recursive witness construction or the new untouched-fibre leaf proof.

The final single interface,
`attachedSelectedPicture_circulation_cycle_transfer` in
`TrainActualCirculationCycleTransfer.lean`, combines the two alternatives:
the full witness bound, or singleton witness wagons and the actual
zero-cut/reduced-supreme/mixed-bridge certificate. It uses the same cutoff
for the original source and old picture. Independent inspection found
no output-supremacy callback or concealed full witness bound in the
bottom alternative. This exact declaration compiled and its dedicated
strict axiom audit passed.

## New proof modules in the validated branch

- `Girth/TrainActualSimultaneousSegmentTransfer.lean`
- `Girth/TrainActualOriginalTwoCycleSupreme.lean`
- `Girth/TrainActualOutputGirthFromOriginalTwo.lean`
- `Girth/TrainActualTwoCutPairEdgeGeometricSupreme.lean`
- `Girth/TrainActualTwoCutStandardCoreReducedSupreme.lean`
- `Girth/TrainBottomReducedSupremePieces.lean`
- `Girth/TrainActualBottomReducedTransfer.lean`
- `Girth/TrainActualCirculationCycleTransfer.lean`

## Remaining mathematical boundaries

The corrected untouched-fibre **conclusion** is revalidated, but its new
leaf-separator derivation is not separately formalized. The transfer
used inside bottom forest-to-order conversion is now checked, but its
preceding minimum-segmentation and forest-to-reduct construction are
not thereby certified. The local conditional circulation theorem is
checked; the full recursive construction supplying every witness,
compatibility condition and global invariant remains a separate task.
No EPPA-valuation or successor-tree replacement is needed by the
checked simultaneous-transfer argument.
