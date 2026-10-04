# Main-draft formalization coverage

Source manuscript: `janhubicka/girth`, current `main.tex` entry point.

| Manuscript item | Lean status |
| --- | --- |
| §1 embeddings / image copies | represented by `RelStructure.Embedding` and `Girth.copyCarrier` |
| §1 support hypergraph | `Girth.supportCopies` |
| §1 A-linear support | `Girth.ALinear` |
| §1 A-strongly induced | `Girth.AStrong` |
| §1 Berge cycle / girth (>g) | `Girth.BergeCycle`, `Girth.GirthGT` |
| girth (>2) implies linear support | proved by `pairwise_subsingleton_of_girthGT_two`, `aLinear_of_girthGT_two` |
| subhypergraphs preserve a girth lower bound | proved by `girthGT_of_subset` |
| §1 A-supported tree amalgam | `Girth.ASupportedTreeAmalgam` |
| A-supported ⇒ generic tree amalgam | proved by `ASupportedTreeAmalgam.toTreeAmalgam` |
| irreducibles / A-copies in supported trees lie in constituent B-copies | proved by `irreducible_contained_in_copy`, `aCopy_contained_in_copy` |
| finite copy containment forces equal carriers | proved by `sameCopy_of_range_subset`; supported-tree specialization `bCopy_same_constituent` |
| A-copy coverage in supported trees | proved by `ASupportedTreeAmalgam.aCopiesCoveredByB` |
| A-linearity + controlled B-intersections imply B-copies are A-strong | proved by `aStrong_of_linear_and_controlled` |
| supported-tree B-copy intersections are controlled | proved by `ASupportedTreeAmalgam.bIntersectionsControlled` |
| singleton B-copy intersections are A-supported on both sides | proved by `ASupportedTreeAmalgam.singletonIntersectionsSupported` |
| §2 EHN / partite structural input | imported from pinned `partite-construction`; its formalization there is still being strengthened |
| Ramsey + generic bounded local-tree + irreducible coverage core | `localTreeRamseyCore` |
| Lemma 2.1 geometry of A-supported tree amalgams | fully proved; `ASupportedTreeAmalgam.girthGT`, `bIntersectionsControlled`, `singletonIntersectionsSupported`, `aLinear_of_base_and_controlled`, `aStrong_of_linear_and_controlled` |
| Observation 2.2 closure expansions | actual c_A expansion and `IsClosed ↔ AStrong` proved; relational free-amalgam geometry over strong bases now encoded through CI; final full-function free-amalgam packaging remains |
| Theorem 2.4 A-linear Ramsey theorem | actual c_A/c_B expansion, relational A-copy lift, closed-set classification, full-embedding closedness, A-strongness, and pairwise controlled intersections formalized; external class-Ramsey/free-amalgamation input remains |
| §4 forest of copies / join trees | definitions, running intersections, leaf-attachment equality, canonical rooted paths, parents, and parent-level equation formalized |
| §§3–6 induced picture/local-forest construction | not yet formalized |
| Main Theorem 1.1 | not yet formalized |

The dependency on `partite-construction` is pinned deliberately.  As the EHN
and recursive/iterated construction formalization there advances, this project
can bump the pin and replace assumptions or wrappers by stronger checked
interfaces.
