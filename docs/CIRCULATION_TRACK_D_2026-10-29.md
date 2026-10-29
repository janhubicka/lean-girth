# Track D: forest conversion and recursive witness assembly

Common base: `3af405cc3a51ca7d3201e221a8a2a56d2e443751`.
Branch: `circulation-par-d-forest-recursion-oct29`.
Contract: issues #663 and #664, with the audit in #665.
Scope: circulation only.

## Validation state

This is an implementation checkpoint. Kernel compilation and axiom audits
are in progress; the branch must remain draft until they succeed on its
latest head. The new lane-local workflow compiles the new modules and audits
their exports without changing the shared umbrella, `lean.yml`, or manuscript.
No final train Ramsey theorem is claimed by this checkpoint.

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

The remaining applications include the minimal-segmentation length estimate
in the forest-to-order picture step, its cycle-transfer hypotheses, the actual
initial/refinement/cutoff-two construction operators, and their A/B/C
integration. No uncovered ambient edges are pruned at higher coordinates.

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
- The finite pass transports selected labels and all train relations, rather
  than inferring those properties from an ordinary relational embedding.

## Reproduction

Run `bash scripts/check_track_d.sh` using the pinned toolchain and dependency
revisions. It builds all new theorem modules, runs their `#print axioms`
exports through `scripts/check_axioms.py`, and runs all four existing finite
boundary regression programs. Shared full-repository CI remains independent.
