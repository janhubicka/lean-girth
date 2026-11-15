# Numbered Track 2: proof chain and remaining validation gates

Status: **source-level candidate, not kernel-verified** (updated 14 November 2026).

## Exact sources and separation of branches

- Frozen circulation reference: `janhubicka/girth/main@8c9cfa6eb6d817a08f3009fe048fc0be07426ece`, reachable-source digest `45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec`.
- Unmerged current paper edits: [`edit/track2-reconciled-20261115`](https://github.com/janhubicka/girth/tree/edit/track2-reconciled-20261115), rebased on `girth/main@ca43c0b2abf42f4e49823d02f3106cec9378ec0d` (15 November 2026); this preserves the independently rewritten cutoff-three proof. The frozen reference is not modified.
- Unmerged Lean candidate: [`validation/2-forest-trace-20261115`](https://github.com/janhubicka/lean-girth/tree/validation/2-forest-trace-20261115), rebased on `lean-girth/main@733d3c80e2d86feb5d2721fa85300088297e00a7` (15 November 2026). The previous `98e40142` source candidate is preserved on its historical branch; this branch contains its checked-for-overlap source files and newer interface adapters.
- No paid GitHub Actions checks launched. This checkout did **not** run Lean; local compiler/mathlib binaries are unavailable. The exact candidate `#print axioms` commands are in `Girth/CheckTrack2Trace.lean`, but have not been executed.

## Exact theorem chain

| Manuscript role | Candidate / existing Lean source | Contract |
| --- | --- | --- |
| `lem:foresttracegirth` | `ForestTraceAcyclic.girthGT_union_of_forest_edge_traces`, `girthGT_selected_of_forest_edge_traces` | Linear H, edges of size ≥2, every member traces at most one H-edge, selected edges occur as whole traces. Uses checked `girthGT_union_of_forest`; avoids another leaf induction. |
| Indexed finite Berge-cycle contradiction | `ForestActiveTraceGirth.girthGT_of_bounded_smallOrWhole_forest_completions` | Turn a cycle into an injectively indexed family of mandatory edges; complete it, then pull back acyclicity. |
| **Actual forest completion → active girth** | `ForestCompletionTraceBridge.girthGT_of_forestCompletion_designated_traces` | Consume the existing `ForestCompletionProperty` and `ForestCompletionWitness` records. Selected A-edges lie wholly inside S; require the boundary classification only for *added designated B-members*. The earlier stronger all-tested-piece version was removed. |
| Actual selected B boundary | `ForestActiveTraceBoundary.projectedBCopy_smallOrWhole_activeBoundary` | The existing `projectedCopy_activeCarrier_intersection_classify` plus actual membership in the B-member's own A-support, not merely carrier intersection. |
| True **old** active subsystem girth | `ForestOldActiveGirth.oldActiveSupport_girthGT_of_designatedCompletion`, `oldActiveInduced_girthGT_of_designatedCompletion` | Exact designated A/B piece predicates; old A-linearity, base B-projection A-strongness, genuine finite completion, two distinct vertices of A. Recover the actual induced active support via the existing mapped-support equivalence. Does **not** assume processed-output girth. |
| Structural step already implemented conditionally | `ForestStructuralABCompletion.assemble_actual_AB_from_local_copy_cover` | Reuse the old completed picture and an actual local witness with A-copy coverage, local forest bound and output A-linearity. The generic join-tree lemma's singleton-helper refinement is **not** needed to apply this theorem to the edge-covered structural construction. |
| Direct increment | `ForestActualRecursiveIncrement.actualPartiteDesignatedAB_mixedForest_of_relationalLocal` | A local witness, q=2 base versus q≥3 predecessor, whole gluing-image strongness, and independent output A-linearity/girth two. Do not derive the ambient girth assumption circularly from the desired forest. |

## Adversarial audit conclusions

1. The active-girth conclusion is about the *old* induced subsystem `(C.induce S).toRelStructure`, not `ProcessedActiveGirth.processed_activeSubsystem_girthGT_of_local`, which concerns the *new processed* subsystem.
2. The image edge set `H` must be exactly `mappedSupportCopies A (C.induce S) C incl`, rather than all ambient A-support edges or an arbitrary set of labelled edge occurrences. The endpoint constructs its containment, image-membership and reflection proof.
3. A designated B-copy's boundary must be a genuine complete A-support edge of that B-piece. The existing factorization `bSupportPiece_eq_embeddedACopySupportPiece` supplies this.
4. For the **general** `lem:joinlift`, the older `forestOfCopies_lift_local_of_linear` is too strong on singleton separators. A new direct leaf-induction source candidate (`ForestGeneralJoinLift`) now proves the required labelled forest without singleton helpers; `ForestRetainedSetLift` handles duplicate and omitted one-edge members. This is independent of the simpler edge-covered structural application.
5. Retain requests that are also selected or added local-completion members. Deleting such members would change the claimed result. No arbitrary-subfamily heredity is available.
6. There is **no new kernel certification yet**: a well-typed-looking Lean source candidate, a text audit and finite diagnostics cannot establish that Lean elaborates the statements or that `#print axioms` is clean.

## Exact completion gates

From a checkout of this candidate branch with the pinned toolchain and mathlib cache:

```bash
LEAN_NUM_THREADS=1 lake build Girth.CheckTrack2Trace
lake env lean Girth/CheckTrack2Trace.lean
```

After a successful compilation, inspect the printed assumptions of every new theorem, reject `sorryAx` and unapproved axioms, and record source commit and exact imported declarations. The finite-set A/B-copy-to-support adapter is also present as a source candidate (`ForestOldActiveSetGirth`). Check both its nonempty and empty finite-selection cases in a real Lean build. Only then promote a validation marker for `lem:puresubsystem`. The general `lem:joinlift` now has a retained finite-SET source candidate; exact Lean compilation, detailed manuscript-to-type matching, and end-to-end `prop:certpres` remain open.

## Reproducible finite tests

The paper branch's `validation/numbered-tracks/check_trace_and_singleton.py` covers triangles and squares with 0–2 auxiliary member carriers; the negative square test was independently executed locally with 667 configurations and all possible labelled trees. It is a bounded counterexample diagnostic, not a general proof.

## 14 November continuation: source-level repairs

- The original cycle argument passed `Fin c.length : Type 0` to a
  `ForestCompletionProperty` indexed in `Type v`. The revised
  `girthGT_of_bounded_trace_forest_completions` instead uses the finite
  subtype `{e : Set W // e ∈ Set.range c.edge} : Type v`.
  The surjection from `Fin c.length` to that subtype proves
  the cardinal bound, while `Subtype.val` injectivity distinguishes
  physical cycle edges. The relevant Mathlib
  `Fintype.card_le_of_surjective` API was checked in public Mathlib
  source; **Lean elaboration of this candidate was not run**.
- `Girth/ForestFiniteSetCompletion.lean` now defines
  `FinsetForestCompletionProperty` and its
  `FinsetForestCompletionProperty.toIndexed` theorem.
  Its proof takes the image of an arbitrary finite indexed
  selection and uses `Finset.card_image_le` to control
  repetitions without an injectivity assumption.
- `Girth/ForestOldActiveSetGirth.lean` gives the
  `oldActiveInduced_girthGT_of_supportFinsetCompletion`
  endpoint, invoking the preceding finite-set adapter
  and the existing `oldActiveInduced_girthGT_of_designatedCompletion`.
  This is a precise **support-set** interface, not yet an
  identification of actual relational copies with their support pieces.
- Removed the unused generic A-strong one-edge-boundary lemma
  from `ForestActiveTraceBoundary.lean`. Only the
  projected-designated-B boundary statement is needed:
  the selected A-edges already lie inside the old active subsystem.
- The paper edits were copied onto the **current editorial main**
  in [`edit/track2-forest-trace-rebased-20261114`](https://github.com/janhubicka/girth/tree/edit/track2-forest-trace-rebased-20261114);
  this preserves parallel Track 3, 7 and 8 changes. The old
  41-page digest is the frozen baseline, not the digest of
  the new branch. The English proof of `lem:foresttracegirth`
  was shortened to the same trace-piece/forest-union argument
  used by the Lean candidate.

The exact source and axiom gate still need a focused, **real**
Lean compilation with pinned dependencies. The source edits
are not evidence of a successful kernel check. Do not upgrade
validation markers yet.


## 14 November — actual copy-set interface closed as a conditional theorem

The candidate now adds two direct **source-level formal adapters**.

- `Girth/ForestCopySetCompletion.lean` defines
  `FinsetLabelForestCompletionProperty` for finite SETS of labels of
  actual copies, measured using the **complete support-piece** forest.
  Its `toSupportIndexed` theorem takes any finite indexed family of
  selected support pieces, chooses a genuine copy label for each
  tested support, takes the finite set of chosen labels, applies
  copy-set forest extension, and returns the existing
  `ForestCompletionProperty` with all selected pieces surviving
  and every extra member designated. The image cardinality is
  at most the original family size, and no support-map injectivity,
  arbitrary subfamily heredity, or fabricated output bound is used.
- The converse `FinsetForestCompletionProperty.toLabelFinset`
  turns any finite-support-set completion property into a
  copy-label-set completion property, again with no injectivity
  assumption on support. This isolates the two natural descriptions
  of the manuscript's finite-set condition.
- `Girth/ForestOldActiveSetGirth.lean` defines
  `pictureABLabelSupport` on the genuine sum type
  `Embedding A C ⊕ DesignatedCopy B D C family`, using a
  one-edge A-piece or the full B-support piece respectively.
  `testedPictureABSupport_iff_label` proves that the
  **tested support predicate is precisely the image of these
  actual labels**. Finally,
  `oldActiveInduced_girthGT_of_actualCopySets` derives the old
  active induced-subsystem girth directly from a finite-set
  forest-extension hypothesis on these labels. No injectivity
  of the support map is assumed.

This closes the **translation between finite actual-copy sets and
the existing typed support-completion invariant**, conditional on the
manuscript's mixed-forest extension hypothesis and the stated base
strongness/linearity assumptions. It does not construct the Ramsey
witness needed in other tracks and it does not certify the paper's
different general singleton-free join-tree statement.

The focused `Girth/CheckTrack2Trace.lean` now contains
`#check` and `#print axioms` probes for all new endpoints,
including the bidirectional set adapters. No local Lean toolchain or
pinned mathlib cache was found in the container; direct GitHub
egress failed DNS. Hence **no new kernel claim is made**, even
where a proof term contains no `sorry`.

The manuscript branch was synchronized again onto the current
source, preserving the separately revised `paper/07-forest-increment.tex`.
Only the independent output-linearity preface was transported into
that proof; the older Track 2 copy of that entire file was NOT
pushed, so the newer cutoff-three result is preserved.

## 14 November — direct forest increment without an output-girth premise

The old `ForestActualRecursiveIncrement.actualPartiteDesignatedAB_mixedForest_of_relationalLocal`
still lists output ambient girth greater than two as a premise. The candidate
`Girth/ForestDirectIncrementLinearity.lean` provides an independent
geometric derivation of that premise before invoking the theorem.

- `Girth/ForestTwoMemberLinearity.lean` proves
  `linearEdgeSet_of_finiteMixedForestThrough_oneEdges` and
  `aLinear_of_finiteMixedForestThrough_oneEdges`.
  Every actual ambient A-edge is tested; for $m\ge 2$, its
  two-member mixed-forest property rules out two different
  support edges meeting in two vertices. Thus old A-linearity
  follows from the OLD forest hypothesis, instead of being a
  new assumption.
- the local girth bound greater than $m\ge 2$ gives local-core A-linearity via
  `pairwise_subsingleton_of_girthGT_two`.
- Base A-linearity, rigid processed A-copy and actual A-strong
  gluing images give global output A-linearity through
  `activeAttachment_geometry_of_base_aLinear`.
  The pre-existing `girthGT_two_of_aLinear` converts this
  to the exact output support-girth-two input of the older
  increment theorem.
- `actualPartiteDesignatedAB_mixedForest_of_strongLinearStep`
  combines these steps and the original conditional direct
  increment for every $m\ge 2$, retaining its honest
  `m=2` local-base disjunction and whole-gluing-image
  strongness assumptions. It neither invokes the desired
  output forest property to prove linearity nor postulates
  a new Ramsey witness.

These are **uncompiled source-level proof candidates** and were
added to `Girth/CheckTrack2Trace.lean` for future exact-head
axiom inspection. They do not promote a manuscript validation mark.



## 14 November — separator cross-intersections and source-level robustness

The proof of the general `lem:joinlift` needs one precise
cross-family step, now separated into candidate
`Girth/ForestSeparatorCrossAllowed.lean` (four theorem
declarations, all in the focused axiom gate):

1. `allowedIntersection_oneEdge_self`: the requested
   `e^+` is allowed to meet itself, so the requesting member
   does not create an exception to pairwise allowedness.
2. `ownEdge_of_allowed_oneEdge_large`: any member meeting
   `e^+` in at least two vertices contains `e` as an
   **edge of its own support**, not merely as a carrier subset.
3. `allowedIntersection_with_local_request`: every
   member of a local forest has this allowed intersection
   with its requested edge, including the member equal to
   the request.
4. `allowedIntersection_cross_of_common_request`: for
   members of two local forests whose cross overlap is
   contained in the same separator `e`, the cross
   intersection is subsingleton, or equals the whole edge
   `e` belonging to both supports.

This justifies the previously compressed line “all cross
intersections are allowed” in the English leaf proof.
The associated manuscript proof now states that implication
explicitly, before asserting running intersection for the
spliced tree. A finite exhaustive check on four vertices
covered 144 admissible cross-family configurations and found
no counterexample. Without the own-edge condition,
`F={a,b,c}` and `G={a,b,d}`, with `e={a,b}` and
neither piece containing `e` as an edge, give a concrete
failure. The bounded test is saved in the manuscript branch
as `validation/numbered-tracks/check_cross_separator.py`.

The short-cycle proof's finite index bound was also made
explicit in Lean:
`card (physical cycle edges) ≤ card (Fin cycle.length)
= cycle.length ≤ m`. This avoids relying on an
unelaborated definitional equality during transitivity.

**Status remains candidate-only.** No local compiler/matching
mathlib bundle is available in this environment. The four new
cross-intersection theorem bodies have not been elaborated,
and no executed `#print axioms` result exists. A direct
recursive general lift and set-normalization source candidate
are described below. The actual edge-covered structural
completion also reuses existing checked components.


## 14 November — general singleton-free join-tree lifting candidate

The generic join-tree lemma has now been reduced to and expressed
using a **complete recursive source-level Lean candidate**, rather
than only its edge-covered structural specialization.

- `Girth/ForestBinarySeparatorLift.lean` contains
  `forestOfCopies_sum_of_subsingleton_overlap`,
  and `forestOfCopies_sum_of_common_edge`.
  They use the existing checked `forestOfCopies_sumBridge`
  theorem. For singleton or empty total cross overlap, one
  chooses connector nodes only if the shared vertex actually
  occurs in both forests; otherwise arbitrary connecting nodes
  work. For an edge (e), the local `e^+` requests remain
  on both sides, and every cross-family intersection of
  size at least two is the whole edge owned by both pieces.
  **No ambient vertex coverage by support edges is required.**
- `Girth/ForestGeneralJoinLift.lean` contains
  `forestOfCopies_lift_local_without_singleton_requests`.
  It uses the existing outer-tree leaf-deletion/parent theorem
  `JoinTree.mem_parent_of_mem_leaf_and_other` and the
  dependent-family equivalence `sigmaSplitAt`. For each leaf,
  the full cross intersection of the locally assembled
  forest with the leaf is contained in its **outer**
  leaf-parent separator. If the separator is subsingleton,
  use the first binary lemma with *no connector request*.
  Otherwise use precisely the two retained one-edge
  requests. This is a direct recursion on
  `Fintype.card Q`.
- `ForestRetainedSetLift` later applies the existing
  short-auxiliary deletion theorem to remove **only**
  omitted one-edge requests after assembling and normalizing
  the whole family.

**Set-valued continuation (added afterward):** The labelled
lift is composed with `ForestDuplicateLabelNormalization`,
`ForestDuplicateLabelGeometry` and `ForestRetainedSetLift`.
Ambient linearity and edge-nonempty local members imply that
only one-edge members can occur under different labels; these
can be deleted, leaving the finite set of distinct pieces.
Removing all omitted one-edge requests leaves precisely the
selected-plus-locally-completed finite set. The exact result is
`forestOfCopies_lift_without_singleton_retained_set`.
The new statements are still source candidates, not compiled.

The two modules have corresponding `#check` and
`#print axioms` declarations in `Girth/CheckTrack2Trace.lean`.
All are **uncompiled** because local Lean/mathlib artifacts and
network egress are absent. No `leanverified` mark was promoted.


## 14 November — exact set-normalization and retained completion

The generic manuscript lift has now been expressed as a complete
**conditional source-level theorem chain**; no extra singleton
connector or copy-uniqueness axiom is postulated:

1. `ForestDuplicateLabelNormalization.finiteImage_of_duplicate_oneEdge`
   takes a forest indexed by arbitrary labels and extracts a forest
   indexed by its **set of distinct underlying pieces**, assuming
   repeated labels represent one-edge members. One representative
   is chosen for each underlying member; all other labels are
   deleted using the previously checked one-edge deletion theorem.
2. `ForestDuplicateLabelGeometry.isOneEdge_of_linear_carrier_subset_edge`
   proves that an edge-nonempty member contained in an ambient
   edge of a linear hypergraph with edges of size at least two
   is itself a one-edge member.
   `duplicatedLocalMember_isOneEdge_of_ambient_linear`
   applies this to repetitions both within a local family and
   across owners. Along the owner path, running intersection
   puts the repeated member in a separator; the outer allowed
   intersection and ambient linearity force it to be one-edge.
3. `forestOfCopies_lift_local_without_singleton_on_set`
   combines (1) and (2) with the direct recursive forest lift.
4. `ForestRetainedSetLift.restrict_to_retained_finset`
   removes only the omitted one-edge members from a forest on
   the finite image set, and reindexes the survivors by their
   **actual underlying piece**.
   `forestOfCopies_lift_without_singleton_retained_set`
   combines all steps. Its retained-set parameter may be
   instantiated with the union of selected members and local
   designated completion additions; it has no singleton-edge
   coverage premise.

The English `lem:joinlift` now uses **labelled** disjoint unions
in its leaf induction (bridging, rather than identifying, the
two copies of each requested edge), followed by one-edge
duplicate deletion and removal of unselected requests. It keeps
`\mathcal F_Q = \mathcal N_Q \cup \mathcal R_Q \cup \mathcal X_Q`
explicit, with `\mathcal R_Q` the requested edges. This
matches the proposed Lean construction directly.

A bounded executable regression for the two binary joins
(`validation/numbered-tracks/check_binary_separator_gluing.py`)
includes 7,224 singleton/empty-cross cases and 177 whole-edge
cases, with up to two labelled members on each side over
four vertices. No counterexample was found. The model explicitly
distinguishes carrier inclusion from actual ownership of
the separator edge. These finite tests are not general proofs.

**Verification status:** 33 candidate theorem declarations currently
have 33 corresponding `#print axioms` checks in the focused
gate; none has been executed, and no new source has been
Lean-compiled. No `sorry` or `admit` tokens were found in
the new modules during static inspection. A successful
exact-head build and axiom inspection is a hard prerequisite
to promoting `\leanopen` or calling Track 2 validated.


## 15 November — empty outer family, independent Lean gates, and three-owner test

**Exact statement repair.** The manuscript's lifting lemma permits
an empty outer family; the first recursive candidate required
`Nonempty Q`, because it takes a `JoinTree P` as data.
`ForestRetainedSetLift.forestOfCopies_lift_retained_set_including_empty_outer`
now separates the empty case from the nonempty chosen-tree case.
The empty case proves the retained family has no labels and is
therefore an empty forest. The manuscript proof now states this
base case explicitly. The wrapper does not posit a join tree on
an empty outer set and retains exactly the former hypotheses in
the nonempty case.

**Independent kernel gates.** The full
`Girth/CheckTrack2Trace.lean` still prints axioms for all
**35** source-level candidate theorems. The inventory is
partitioned without omissions or overlaps into:

- `Girth/CheckTrack2ActiveGirth.lean` — **14** declarations.
- `Girth/CheckTrack2DirectIncrement.lean` — **3** declarations.
- `Girth/CheckTrack2JoinLift.lean` — **15** declarations.

A focused local runner, `scripts/check_track2_local.sh`,
uses the already tracked `scripts/check_axioms.py` and
accepts `active`, `increment`, `join`, or `all`.
In `all` mode it runs the independent gates even if an earlier
one fails, then the full integration check only if all three pass.
Each gate must both elaborate and report only `propext`,
`Classical.choice`, and `Quot.sound`; the strict checker also
requires **every expected theorem** to appear in the output.
It does not explicitly update dependencies or invoke GitHub Actions. Restore the pinned local cache first: Lake itself may attempt to fetch missing packages.

```bash
bash scripts/check_track2_local.sh active
bash scripts/check_track2_local.sh increment
bash scripts/check_track2_local.sh join
bash scripts/check_track2_local.sh all
```

**Adversarial finite regression.** The manuscript branch now
contains `validation/numbered-tracks/check_three_owner_join_lift.py`.
It exhausts 37 valid local forests at each of the first two
owners and one at the third, for **1,369** three-owner
configurations. One outer link is a full support edge; the next
is a singleton. In **185** configurations the middle local
family does not contain the singleton connector. The test checks
foresthood before and after normalization to distinct pieces
and deletion of the omitted one-edge request. It also checks
the empty family and an explicit counterexample to deletion
of a multi-edge designated member. All assertions passed in
the current container. These are **finite checks**, not Lean
certificates.

**Current blocker.** This container does not have Lean, Lake,
Mathlib objects, or DNS access to download their pinned
artifacts. Hence none of the 32 new theorem declarations has
been elaborated, and none of its `#print axioms` results has
actually been inspected. The three gates and full integration
check must run against an exact local checkout before promoting
any validation marker. The existing conditional forest-completion
components remain separate from the still-unconstructed local
witnesses in other tracks.


## Exact hypothesis audit — source candidates versus the manuscript

This table is **statement correspondence**, not a kernel certificate.

| Candidate input | Source in the revised English proof | Audit result |
|---|---|---|
| `PairwiseAllowed P` | The outer family is a forest, and enlarging each (Q) to (P_Q) preserves exact pairwise intersections; whole-edge intersections remain supported edges | Follows from the set-up; no new assumption |
| `IsEmpty Q ∨ ∃ JOuter, hEdgeRequest` | Empty outer family is trivial. Otherwise choose the stated outer join tree, requesting (e^+) only for separators of size at least two | Exact after the empty-family wrapper; no singleton connector |
| `hLocal`, `hContain` | Each (mathcal N_Q ∪ mathcal R_Q ∪ mathcal X_Q) is a forest inside (P_Q) | Exact local completion hypothesis |
| `hLinear`, `hLarge` | The common ambient hypergraph (K) is linear and every edge has at least two vertices | Choose the Lean edge family (H=E(K)) |
| `hOuterEdges`, `hLocalEdges` | The outer and local pieces are subhypergraphs of (K) | Directly inherited |
| `hLocalNonempty` | All selected and locally added members contain an edge; every requested (e^+) is also edge-nonempty | Explicitly stated; needed to delete duplicate labels |
| `hKeepSub`, `hOmitted` | Retain precisely (mathcal N∪⋃_Qmathcal X_Q); every other member of the full local union is a one-edge request | Follows by classification, including when a request is selected or added |
| `hOldLinear` and base `hBaseStrong` in active girth | The picture is (A)-linear and its designated base projections are (A)-strong by construction | Standing picture invariants |
| `u≠w` in active girth | The theorem is applied in the (|A|≥2) case; it excludes one-vertex edges | Existing case distinction, not a new global premise |
| `hCoreGirth`, `hLocalStrong`, local ((m-1))-forest in direct increment | The actual local witness has girth (>m), strongly induced gluing images, and the previous mixed forest property | Genuine local witness obligations, not furnished by Track 2 alone |
| `hRigid` in direct increment | The processed (A)-copy is rigid in the ordered setting | Derivable from the ordered hypothesis |
| Output support girth (>2) | Deduce old linearity from two-member forests, core linearity from core girth, then output linearity by the checked attachment theorem | No circular premise in `ForestDirectIncrementLinearity` |

The main mathematical interfaces are therefore *represented* by
conditional Lean theorems, rather than being hidden in shorthand.
The direct local Ramsey witness and full manuscript induction remain
external construction obligations. **Do not interpret the table as
evidence that the new Lean proofs compile.**

The new local gate is split into disjoint import subgraphs:
active girth (16 source declarations), direct increment (3), and
general lifting (16). Their new-module dependency graphs have
no cross-imports. In this environment the local runner passed
a Bash syntax check and correctly reported missing Lake with
exit code 2; no Lean elaboration or strict axiom run took place.

## 15 November — clean nonconflicting rebase and four-owner stress test

Both Track 2 working branches were transplanted onto their current main baselines
after checking that other tracks touched none of the Track 2 files.
New branches: `validation/2-forest-trace-20261115` (base `733d3c80`)
and `edit/track2-reconciled-20261115` (base `ca43c0b2`).
No unverified Track 2 code was merged.

The paper regression `check_four_owner_join_lift.py` uses four outer owners
with support-edge, singleton, and support-edge separators. Deterministic
seed `20261115` generated **45,000** choices of local completions.
For each, the labelled union, distinct physical member image and four
permitted one-edge-request deletion patterns were tested (180,000 deletion
checks); no failures occurred. Of these tests, 6,901 lacked a singleton
connector at the first middle owner and 7,003 at the second middle owner.
These are bounded Python tests, not Lean validation.

The kernel obstacle remains: no `lean`/`lake` binaries, no pinned Mathlib
cache, and failed direct GitHub DNS resolution. The 32 source-level
candidate declarations remain **unverified**.
## 15 November — remove unused join-tree side lemmas

Two wrapper declarations were not on any path from the general lift to
its retained-set conclusion: `forestOfCopies_sum_of_smallOrEdge_overlap`
and `forestOfCopies_lift_without_singleton_then_delete`. Both were removed
from the active validation branch and from its full/focused axiom gates.
The previous source is preserved on the historical Track 2 branch.
The proof-critical binary gluing, recursive lift, duplicate elimination,
and retained-set endpoint remain unchanged.

The gate is now **32 candidate theorem declarations**:
active girth 16, direct increment 3, general join-tree lifting 16.
The reduction removes code that could otherwise block Lean elaboration
without contributing to any final theorem. No fresh kernel check has run.
## 15 November — forest extension itself implies old A-linearity

The old active-girth lemma in the paper assumes A-linearity separately.
For cutoff `m >= 2` it also follows from the very forest-extension
invariant already used in the girth argument. Choose two distinct
ambient A-support edges `e,f`. The completion predicate for these
two one-edge pieces retains both in the same forest; their member
intersection must be subsingleton or a shared support edge.
One-edge ownership makes the latter imply `e=f`, a contradiction.
Thus all different A-support edges meet in at most one vertex.

Candidate `Girth/ForestCompletionTwoEdgeLinearity.lean` contains
`linearEdgeSet_of_twoEdgeForestCompletion` using an index type
`PUnit ⊕ PUnit` at the **ambient universe** (avoids `Fin 2`
universe ambiguity). The stronger endpoint
`oldActiveInduced_girthGT_of_actualCopySets_without_oldLinear`
was added to `ForestOldActiveSetGirth.lean`. It deduces old ambient
`ALinear` from the copy-set completion predicate, then reuses
the original old-active girth proof and its designated boundary
classification. It requires the correct `2 <= m` cutoff explicitly.

The two declarations are added to the **active** and full axiom
gates. This is source-level strengthening; until Lean elaboration
and `#print axioms` pass it must not be reflected by a green
validation mark or by weakening the manuscript's frozen hypotheses.

**Sharpness of the cutoff.** The assumption `2 <= m` is essential
for deriving linearity from completion. For `m = 1`, let the
ambient edge family contain `{0,1,2}` and `{0,1,3}`.
Every requested singleton one-edge family is already a forest
(so the completion property through one holds with no extra
designated members), but the two edges share two vertices and
the ambient family is not linear. A finite four-vertex sanity
check inspected all 55 pairs of distinct support edges of size
at least two: 28 pairs obstruct linearity and therefore cannot
survive together in a two-member forest completion.
That check is not a Lean certificate.


## 15 November — source-level reconciliation after Track 1 verification

The latest manuscript main gained a **verified Track 1** theorem
`Track1CutoffThreeReuse.track1_three_boundaries_forest_of_core`
in `paper/07-forest-increment.tex`. The earlier Track 2 branch
still carried its obsolete open annotation at that point.
The reconciled manuscript branch
`edit/track2-reconciled-20261115` starts from current
`girth/main@e789e881b10ded74d279a77ab0223c1f01ceff82`,
**preserves that verified annotation and all Track 1 proof content**,
and applies only the independent Track 2 output-linearity preface
and its unverified mark to the direct increment.
No obsolete TODO/\leanopen marker was re-added over Track 1's certificate.
The old Track 2 manuscript branch remains as historical source.

## 15 November — adversarial dependency on irreducible coverage

The generation part of manuscript `lem:puresubsystem` currently uses
the **strong** picture invariant: every irreducible substructure
is inside a designated B-copy. The active-girth argument
developed in Track 2 does NOT use this irreducible-cover premise.

The main Lean library already contains
`ForestMixedIrreducibleCoverage.DesignatedBorACoversIrreducibles`
and `ForestMixedActiveGenerated.activeSubsystem_aGenerated_of_mixedCoverage`.
They establish a weaker but more robust B-or-A coverage route
for a local picture that is not pruned to designated B-copies.

The manuscript's `prop:certpres` invokes
`cor:structforestres(ii)` to assert that EVERY local A-copy
in the new core belongs to a selected gluing copy. Under
that explicitly stated stronger local output, the original
designated-only irreducible-cover proof applies. But if
the recursive local witness is available only in the
nonpruned A-generated form, that coverage step is not automatic.
Use the checked mixed-cover bridge rather than silently
assuming A-edges belong to selected gluing B-copies.

**Boundary:** This is a dependency on the *actual local witness*
from other validation tracks, not a new hypothesis in the
Track 2 trace-girth or forest-lifting lemmas.
No black/frozen proof text was changed on this basis.
