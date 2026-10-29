# Track D: forest conversion and recursive witness assembly

Common base: `3af405cc3a51ca7d3201e221a8a2a56d2e443751`.
Branch: `circulation-par-d-forest-recursion-oct29`.
Contract: issues #663 and #664, with the audit in #665.
Scope: circulation only.

## Validation state

This is an implementation checkpoint. The complete new proof bodies have
passed exact-source Lean diagnostics and their axiom audits, using the
pinned toolchain and genuine dependencies. These diagnostics do not replace
the original-import build. The first remote build compiled the generic
forest-cycle modules, then exposed two field-notation line-break errors in
the relational support and selected-pass interfaces; these are repaired.
The original-import build and latest-head CI remain required before review.

The new lane-local workflow builds every repository module and audits all
new exports without changing the shared umbrella, `lean.yml`, or manuscript.
The independent audit #665 revealed a pre-existing unclosed reflexive goal
in `RootedForest.parent_dist_add_one`; the only old proof-file edit here is
the one-line reflexivity closure, with its own axiom check. No final train
Ramsey theorem is claimed by this checkpoint.

## New mathematical work

1. `ForestCyclicSwitching` proves the cyclic leaf-cut combinatorics, including
   wraparound: a mixed binary cyclic word switches twice, and switches confined
   to two consecutive positions force an actual singleton side.
2. `ForestToSupremeBottom`, `ForestToSupremeLeaf`, `ForestToSupremeOwned`, and
   `ForestToSupremeCycle` implement the forest-cycle lemma. The conclusion is
   literal globally legal simultaneous supremeness. Repeated occurrences are
   permitted. The two-occurrence case is handled directly, while larger cycles
   use actual join-tree leaf deletion and actual short replacements.
3. `ForestBottomSupremePullback` pulls a later supreme label back across legal
   bottom relabellings with unchanged connectors and no new designated
   occurrences. Injective bottom parents rule out long pieces; the existing
   short-only assembly theorem verifies global legality.
4. `ForestActualRecursiveSupport` constructs the relational support maps and
   true-active support coverage required by the existing increment theorem.
   `ForestActualRecursiveIncrement` applies that theorem to exactly the
   transported selected B-copies and every ambient A-edge.
5. `ForestToSupremeActualGeometry` instantiates bottom geometry for genuine
   selected-picture data and relates physical mixed forests to labelled
   bottom forests. Physical designated-copy injectivity is explicit in the
   generic bridge and is derived for finite ordered targets. The multi-edge
   case is separated from the one-edge case.
6. `TrainRecursiveWitness` assembles data-valued witnesses using the existing
   multiplicity-lex order. It separates `[2]`, `2 :: nonempty_tail`, and the
   `q > 2` case. Each larger-cutoff request has arbitrary positive depth and
   a smaller rank; forest-to-order conversion is a fixed operation on an
   already established vector.
7. `TrainRecursiveWitnessPass` carries actual finite selected pictures,
   mixed bottom forests, all tail system-girth conditions, adjacent train
   parameters, target-train preservation and reflection, selected-copy
   provenance, and the colouring arrow through a finite partite pass.
   Its remaining-profile readiness predicate permits the actual unprocessed
   refinability invariant; it does not assert that every arbitrary stage
   is refinable.
8. `ForestOrderSegmentBudget` proves the missing numerical estimate:
   if the literal cyclic segmentation has no mixed singleton segment, then
   twice its segment count is at most the source's twice-order. A source of
   order at most `q` therefore has a reduced cycle of length at most `q`.
   The source and reduct may have different incidence data. The combined
   theorem supplies supremeness of the acceptable reduced bottom cycle;
   physical transfer to the source remains separate.
9. `ForestSelectedMixedCoverage` preserves irreducible coverage by selected
   B-copies or ambient A-edges through the actual attachment. Its active
   generation corollary needs base strongness only for selected old copies.
10. `TrainRecursiveWitnessInitial` identifies all actual initial support
    edges with component/target-edge pairs, constructs the component train
    with universal top, and proves exact restriction to each selected
    target copy. It also proves initial selected support injectivity,
    selected strongness and mixed coverage, support coverage/nonemptiness
    from explicit target hypotheses, and disjointness of distinct A-copies
    in each initial projection fibre.
11. `TrainRecursiveWitnessInitialParameters` identifies each proper-cut
    initial wagon carrier with its tagged target carrier and derives all
    adjacent initial parameters from the target parameters under each
    prescribed base projection. The universal top is handled explicitly.
12. `TrainRecursiveWitnessProfiles` realizes each inhabited injection profile
    as an actual relational embedding into the base, supplies the empty-fibre
    identity step, and converts constructors indexed by actual embeddings
    into the finite pass's profile-indexed step. It also supplies a finite
    nodup enumeration of profiles and extracts a nonempty prescribed family
    from its restricted Ramsey arrow.

## Noncircular dependency boundary

The forest-cycle theorem assumes only the actual bottom physical geometry,
acceptability, and a forest on the distinct labels which occur. It does not
assume supreme pieces or the desired system-girth bound. The local-forest
corollary separately requires a length bound `n ≤ q`: order at most `q`
alone only gives `n ≤ 2*q` and cannot be substituted for that premise.

The increment bridge reuses
`actualPartiteDesignatedAB_selectedForest_of_trueActiveOldFull` and its
lower kernels. It retains the genuine local embeddings, strongness, old
forest bounds, and ordinary-girth premises. It does not establish their
Ramsey existence or infer tail system-girth from ordinary girth. At cutoff
two the predecessor forest bound is automatic; the larger case uses the
actual local mixed forest with physical copy indices.

The recursive assembly remains conditional on four named construction
operators: the `[2]` base, the shorter-train cutoff-two pass, the larger-cutoff
pass, and forest-to-order conversion. The finite-pass theorem discharges
iteration and backwards selection, but its local geometry-preserving
`PictureStep` operator must still be constructed. Neither theorem substitutes
rank decrease for witness existence.

The numerical minimum-segmentation length estimate is now proved from exact
word identities and absence of mixed singletons. Constructing the actual
geometric segmentation and proving those hypotheses remain separate. No
uncovered ambient edges are pruned at higher coordinates.

## Exact remaining construction obligations

| Construction boundary | Proved here | Still required |
| --- | --- | --- |
| Forest cycle | Acceptable bottom cycle carried by its occurring labelled forest has a globally legal simultaneous supreme copy, including repeats and length two | For an order-one reduct without A1, use the separate both-bridges theorem; do not treat it as acceptable |
| Same-cutoff forest-to-order step | Segment count is bounded by source order after excluding mixed singleton segments; actual reduced forest yields supremeness | Physical minimum segmentation, elimination of mixed singletons, source/reduct word identities, old-standard supreme bound, and legal source pullback from Track A |
| Actual forest increment | True-active support, strong support maps, exact full pieces/overlaps, selected B transport, every ambient A-edge, and predecessor forest at cutoff two | Old mixed forest; selected-base strongness; local-image strongness; core ordinary girth `>m`; independent output ordinary girth `>2`; larger-cutoff local mixed forest and physical injectivity |
| Initial picture | Full physical edge equivalence, train, all adjacent parameters, selected restriction and strongness, mixed coverage, support conditions and matching fibres | Mixed forest through the target budget, tail system-girth, and the actual refinement readiness invariant |
| Finite selected pass | Finite profile enumeration and realization, empty-fibre identity, forward iteration with `Ready`, backward colour selection, literal selected-copy transport, all-level train preservation/reflection and selected strong Ramsey extraction | A finite geometric base and actual local `PictureStep` constructors preserving the remaining readiness invariant |
| Recursive kernel | Data-valued recursion in all three rank cases; fixed forest-to-order conversion only after a smaller witness exists | Universal actual witness families and instances of all four geometric construction operators |

The construction obligations above cannot be replaced by weaker invariants:

- The Ramsey base needs `ALinear A D`, selected-base A-strongness, finite
  support, controlled intersections and the auxiliary order. The colouring
  arrow alone does not provide this package. The existing closure Ramsey
  theorem in `ALinearRamsey` is the relevant source.
- A fixed-target `ForestTailStage` cannot itself be the universal recursive
  witness family: the active target, refinement depth, train height and
  contracted coloured edge type change in recursive calls.
- Refinement requires actual finite nested partitions and singleton allowed
  parts, with girth at every inserted cut. `RefinementRunCount` supplies
  arithmetic once run data are given; it does not construct that data or
  the refinement. The initial matching theorem is one concrete input.
- Output ordinary girth `>2` must be derived independently before applying
  the forest increment. Deriving it from that increment's conclusion and
  using it as an input would be circular. Likewise, local forest through
  `q-1` alone does not establish core girth `>q`; the refinement-collapse
  construction must provide the extra gain.
- The cutoff-two case with nonempty tail requires uniform first wagons,
  contraction to a coloured edge type, a shorter-train order witness,
  colour-word Ramsey selection, and actual filling/scattering. The existing
  filling carrier invariant does not construct those operations or their
  cycle-transfer proof.
- Track B must supply genuine generated-wagon strongness/linearity and the
  mixed two-standard obstruction. Track C must supply all-level parameters
  and filling/subcopy system-girth transfer. Ordinary girth, equal wagon
  carriers, and unions of individually strong pieces are insufficient.
- The finite actual output needs finite local indexing, local homogeneous
  selection, irreducible-to-A extension, selected physical injectivity,
  target restriction, transition reflection, support, parameters and every
  tail bound. The increment theorem alone asserts no Ramsey existence.
- The profile bridge does not assume readiness is monotone: dropping an
  empty profile still requires the explicit remaining-readiness clause.
  Active-carrier nonemptiness is equivalent to an inhabited fibre only for
  a nonempty source; the bridge retains that hypothesis.
- Finalization still needs one-edge target handling, fine-to-coarse
  predicates and order completion. No appendix assertion is used.

## Review points

- Physical sets and literal labels are different. Arbitrary duplication of a
  multi-edge designated member cannot be inferred from a forest of physical
  pieces; ordered rigidity supplies the relevant actual injectivity.
- Every retained forest member has a literal occurrence of its own label.
  An absent designated label cannot become the supreme copy.
- Replacements retain both boundary incidences and prove adjacent-label
  distinctness; local replacement validity is not used as a substitute for
  global legality.
- Only actual join-tree leaves are removed. No unjustified general forest
  heredity or arbitrary designated-member deletion is used.
- The labelled forest-cycle proof does not require a preselected designated
  root or a two-edge hypothesis on designated members. Existence of a
  designated supreme occurrence follows within the induction. The separate
  physical-set bridge still needs label injectivity and its multi-edge
  separation; this stronger generic statement does not erase that issue.
- The finite pass transports selected labels and all train relations, rather
  than inferring those properties from an ordinary relational embedding.

## Reproduction

Run `bash scripts/check_track_d.sh` using the pinned toolchain and dependency
revisions. It builds all new theorem modules, runs their `#print axioms`
exports through `scripts/check_axioms.py`, and runs all four existing finite
boundary regression programs. Shared full-repository CI remains independent.
