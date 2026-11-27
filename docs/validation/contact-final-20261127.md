# Local validation of the contact-graph proof — 27 November 2026

## Verified scope

The complete new main proof is kernel-checked locally. This is a statement-level
verification of the final Ramsey witnesses, not just compilation of conditional
construction interfaces. The active source is the `regular-tree-girth.tex`
manuscript in `janhubicka/girth`; its theorem statements were compared with
`main@9eedb6ed48501754040a9ac64c5363809b05b795`. The regular-tree manuscript
sources were checked again at `main@e3c067e1535e97d81eb3d20a899cc82c4b20c78f`
and are unchanged; concurrent changes to the companion manuscripts are preserved.

The checked chain consists of the recursive train construction, the local-forest
partite lemma, the full finite outer iteration, restoration of isolated vertices
and relation tuples, exact identification of ambient copies, and the final
theorems on literal carrier sets.

| Result | Declaration | Local result |
| --- | --- | --- |
| Recursive train existence | `contactProfileRamsey_wellFounded` | Passed |
| Recursive forest boost | `contactProfileForestRamsey` | Passed |
| Local-forest partite lemma | `contactLocalForestPartite` | Passed |
| Qualitative outer Ramsey construction | `contactOrderedOuterRamsey_qualitative` | Passed |
| Quantitative outer girth construction | `contactOrderedOuterRamsey_quantitative` | Passed |
| Full restored support witness | `contactRelationalSupportWitness_exists` | Passed |
| Relational theorem on actual embeddings | `contactRelationalGirthRamsey` | Passed |
| Relational theorem on literal copy carriers | `contactRelationalGirthRamsey_carriers` | Passed |
| Unordered hypergraph theorem | `contactUniformLocalRamsey` | Passed |
| Completed-order corollary | `contactCompleteOrder_fullCorollary` | Passed |
| Small relational induced substructures, exact vertex bound n | `contact_small_induced_supported` | Passed |
| Small induced subhypergraphs | `contactUniformSmallRamsey` | Passed |
| Edgeless hypergraph target | `contactUniformSmallRamsey_edgeless` | Passed |
| Supported-tree embedding implies chordal comparison graph | `contactComparisonGraph_chordal_of_supportedTree_embedding` | Passed |
| Arbitrary-size induced supported-tree embedding iff chordal | `contact_induced_supported_iff_chordal` | Passed |
| Finer-cut cycle localization | `ContactHypergraphData.finer_cycle_in_one_coarser_wagon` | Passed |
| Proper wagon girth iff parent-by-parent bounds | `ContactHypergraphData.properWagonGirth_iff_parentWagonGirth` | Passed |
| General acyclic-incidence trace trees | `contact_trace_joinTree_of_incidence_acyclic` | Passed |
| General acyclic-incidence node erasure | `ContactJoinTree.erase_of_incidence_acyclic` | Passed |
| Covered ordered linear seed, including isolated vertices | `contactCoveredLinearSeed` | Passed |
| Strongness of complete wagons | `OrderOneData.contact_wagon_strong` | Passed |
| Covered triangulations for arbitrary metric weights | `contactCoveredTriangulation_of_metricG4` | Passed |
| Metric shared-chord equivalence | `contactSharedChordBound_iff_metricG4` | Passed |
| Admissible attachments produce a join tree | `contact_joinTree_of_admissibleAttachments` | Passed |
| Join tree iff an admissible enumeration exists | `contact_joinTree_iff_admissibleRank` | Passed |
| Any specified leaf can be enumerated last | `ContactJoinTree.exists_admissibleRank_leaf_last` | Passed |
| Exact one-added-copy completion sharpness | `contactSharp_actual_completion` | Passed |
| Exact vertex-cutoff sharpness with all five witness clauses | `contact_vertex_cutoff_sharp` | Passed |

The full chordality criterion has no size restriction on the induced vertex
set. Its forward and reverse directions, the exact small-size consequence,
and the unordered reductions are checked as separate exported theorems.

## Local build and logical assumptions

The complete local build succeeded with 3,610 jobs. The reproducible command is:

```sh
bash scripts/check_contact_validation.sh
```

This builds `+Girth`, checks all 781 declarations requested by
`CheckContactCore.lean`, the 61 principal declarations requested by
`CheckContactValidation.lean`, and the 48 newly linked manuscript declarations
in `CheckContactManuscript.lean`. The union contains 841 distinct declarations;
the three lists overlap. All checks completed successfully and their
transitive axiom dependencies are subsets of:

```text
propext
Classical.choice
Quot.sound
```

In particular, the audited proofs have no dependency on `sorryAx`, a custom
axiom, or a native computation axiom. The axiom checker also rejects missing
declaration reports, so an incomplete audit log cannot count as a pass.
All six regression tests of that strict checker also passed with
`python3 scripts/test_check_axioms.py`.

The focused default root includes both final main theorems, the corollaries,
and the supporting observations. The CI workflow now runs this complete build
and all three strict audits in addition to its diagnostic component checks.

## Exact dependency versions

The generated `lake-manifest.json` is now retained to pin all transitive
dependencies. Principal versions are:

- Lean: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib: `5bd58ac291422a21f412ae354c91e7d172255a2c`.
- Partite construction: `d2394f65861528f27d68c4a42042285dafef301d`.
- Successor trees: `f9513be1d92782e7a8c45916d32e6e11dc0e0dcf`.
- Ramsey spaces: `54a9eb02f7f7bd2e942e95f7b44fc6f04f48892c`.

The combinatorial Ramsey inputs have proofs in these dependencies, including
finite Ramsey and Hales–Jewett. No Reiher–Rödl girth theorem is an input.

## Repairs and additional verification

The failures in the previous hosted run were repaired without strengthening any
mathematical premise or weakening any conclusion:

- Explicitly retain section parameters used by the outer assembly proofs.
- Lift finite cycle positions to the ambient universe when reindexing a join tree.
- Give dependent tuples and subtype projections their intended types.
- Transport equalities without rewriting the types of their dependent indices.
- Unpack the actual join tree when transporting the selected carrier family.
- Supply the implicit edge parameter in the induced hypergraph piece.

The newly checked small-substructure argument first proves chordality on at most
n vertices from completion of the cycle-side copies. Simplicial elimination
then supplies at most n cliques covering every relation tuple. Their chosen
B-copies are deduplicated before applying the same completion theorem. This
proves an embedding of the full induced structure, including higher-arity and
nullary relations. The empty vertex set is handled separately by an actual
induced embedding obtained from the irreducible-cover clause.

For hypergraphs the order-forgetting map is proved to preserve the actual free
amalgams and supported-tree construction. The source parameter is exactly
`n = max 2 s`. An edgeless target uses the target itself.

For the unrestricted chordality converse, a join tree of maximal cliques is
unfolded into fresh full B-copies, retaining a homomorphism back to the ambient
structure. The induced embedding preserves every relation tuple and reflects
relations through that map. Empty separators are handled by a checked bridge
into the existing supported-tree API; nullary relations and the empty induced
vertex set are included.

The general triangulation observation now permits arbitrary real-valued
weights with zero diagonal and the triangle inequality. Symmetry and positive
weights are not needed. Increasing cyclic restrictions have no larger
perimeter, so the recursive split construction gives covered triangles and
the covered-side and shared-chord conclusions. Its certificate has exactly
`length - 2` triangular faces. The old two-sort split API is preserved.

The enumeration converse uses the exact intersection with the entire
preceding union. Empty and singleton intersections, and a separator contained
in an earlier member, are converted into this equality. The forward proof
uses connected initial subtrees; distance from a root with a finite injective
tie-breaker gives an actual parent-first ordering.

## Sharpness certificates

`contactSharp_actual_completion` checks the manuscript example for every
`g >= 2`. Its ordered B-structure is the cycle on `g + 1` vertices augmented
with the full ternary relation on distinct vertices; A is the ordered edge.
The theorem identifies the actual A-copies with the cycle edges, proves
A-support girth greater than g, and uses an isomorphism from the formal
generated union of the selected edge copies to the explicit source structure.
That union cannot embed into any A-supported tree of B-copies. The ternary
relation also handles the triangle case `g = 2`.

Adjoining the one actual ambient B-copy gives a forest, and the completed
union is isomorphic to B itself. Injective carriers certify the selected and
completed counts `g + 1` and `g + 2`; hence the single added member achieves
the exact equality `(g - 1) * 1 = (g + 1) - 2`. Both necessity and sufficiency
refer to the actual mixed-copy and generated-union APIs used by the theorem.

`contact_vertex_cutoff_sharp` verifies the separate vertex-size example for
every `s >= 4` and every color type. Here A = B is the pure two-point order,
and C is the acyclically oriented chordless s-cycle. The theorem certifies
all five witness clauses at `g = 2` and `n = s - 1`, using the same literal
`ContactCarrierMixedCompletion` API as the main theorem. Its proper selected
families need no added members; A = B carriers are counted only once.
Every irreducible induced substructure lies in an edge, including the empty
and singleton cases. The full s-vertex structure is nonchordal and cannot
embed into a supported tree of the two-point copies. The source assumptions,
including support girth at every finite cutoff, are separately checked by
`contactSharpTwoPoint_input`.

## Important statement distinctions

The main relational witness carries an acyclic distinguished relation
contained in an external linear order; transitivity of that relation is not
assumed. Completing it to a linear order is not asserted to preserve the
irreducible-cover clause. The completed-order corollary has precisely its
stated non-order irreducibility hypotheses.

The completion bound counts distinct newly added carrier sets. When A and B
have the same image, canonical B-tags prevent double counting. The selected
family, its forest, and its cardinality difference are transported together.

The mixed union is the structure generated by the selected copies. It is not
automatically the ambient induced structure on their vertex union; the
small-induced-substructure proof establishes the additional tuple coverage
needed before restricting its embedding.
