import Girth.ContactCore
import Girth.ContactUniformLocalRamsey
import Girth.ContactOrderCompletion
import Girth.ContactComparisonGraph
import Girth.ContactTreeAmalgamChordal
import Girth.ContactSmallRelational
import Girth.ContactUniformTreeReduct
import Girth.ContactSmallHypergraph
import Girth.ContactChordalRelational
import Girth.ContactWagonGirthEquivalence
import Girth.ContactAcyclicTraces
import Girth.ContactManuscriptAdapters
import Girth.ContactMetricTriangulation
import Girth.ContactRootedEnumeration
import Girth.ContactForestInterfaces
import Girth.ContactForestEnumeration
import Girth.ContactCompletionSharpness
import Girth.ContactVertexSharpness

/-!
# Final contact-graph validation target

This target includes the complete recursive train construction, the local-forest
partite lemma, the outer iteration, relational restoration, and the actual
relational and unordered hypergraph Ramsey theorems. It also includes the
order-extension corollary under its explicit irreducibility hypotheses, the
induced supported-tree embedding for vertex sets of size at most n, and the
full chordality criterion for arbitrary induced vertex sets. The
unordered small-induced-hypergraph consequence includes edgeless targets.
The train observations include finer-cut localization and the equivalence
between global wagon-girth bounds and parent-by-parent bounds.
It also includes general acyclic-incidence trace trees and node erasure,
the covered ordered linear seed, and complete-wagon strongness.
Covered triangulations, covered sides, and the shared-chord equivalence
are included for arbitrary real-valued metric weights.
Parent-first admissible enumerations, their converse, and a listing ending
at any specified leaf are included for finite join trees.
The exact forest interface equates allowed separators on tree links with
pairwise allowed intersections in a linear ambient hypergraph, including
the empty-family convention. Its admissible-enumeration equivalence uses
the literal whole-preceding-union attachment condition, including empty
and singleton families and separators.
The completion-budget sharpness example uses actual ordered edge copies,
their generated relational union, and the obstruction to embedding that
union into any supported tree before the containing copy is added.
The vertex-cutoff sharpness witness satisfies all five relational theorem
clauses at n = s - 1 and has an obstructed induced substructure of size s.

`CheckContactValidation.lean` audits the axioms of the principal statements,
including their transitive proof dependencies. The separate component audit
files remain useful for locating a failure. Building only `ContactCore` does
not establish these final application theorems.

-/
