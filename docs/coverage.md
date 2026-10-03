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
| §2 EHN / partite structural input | imported from pinned `partite-construction`; its formalization there is still being strengthened |
| Ramsey + generic bounded local-tree + irreducible coverage core | `localTreeRamseyCore` |
| Lemma 2.1 geometry of A-supported tree amalgams | **in progress; constituent-copy reduction checked** |
| Observation 2.2 closure expansions | not yet formalized here |
| Theorem 2.4 A-linear Ramsey theorem | not yet formalized here; depends on the reusable ordered functional Ramsey interface |
| §4 forest of copies / join trees | next combinatorial layer after Lemma 2.1 |
| §§3–6 induced picture/local-forest construction | not yet formalized |
| Main Theorem 1.1 | not yet formalized |

The dependency on `partite-construction` is pinned deliberately.  As the EHN
and recursive/iterated construction formalization there advances, this project
can bump the pin and replace assumptions or wrappers by stronger checked
interfaces.
