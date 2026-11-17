import Girth.FreePortMidpointClosed

/-!
# Canonical occurrences of closed induced graph configurations

The central distinction in the proposed extension is between SUPPORT
edges E and COLOURED occurrences A. In particular, after an attachment
there may be new induced closed A-copies which cross the interface.
Their occurrence type must be intrinsic to the full output graph, not
restricted to a hand-chosen list of old owners.

A closed induced embedding below is a graph embedding with an
explicit midpoint-closed range. Composition preserves both exact
inducedness and closure. Consequently for a fixed graph A the
type of closed induced embeddings A -> G varies functorially
under closed induced embeddings of host graphs.

This is independent of partite Ramsey theory, and it does not
assert that canonical occurrence completion preserves free amalgams:
new occurrence vertices can appear over mixed private sides.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {U V W : Type v}

/-- A genuine induced graph embedding with midpoint-closed image.
This is the graph-level notion of the coloured occurrence in the
proposed E/A/B-sorted incidence structure. -/
structure ClosedGraphEmbedding
    (A : SimpleGraph U) (B : SimpleGraph V) where
  toEmbedding : U ↪ V
  induced : ∀ u v : U,
    B.Adj (toEmbedding u) (toEmbedding v) ↔ A.Adj u v
  closed : MidpointClosed (adj := B.Adj) (Set.range toEmbedding)

namespace ClosedGraphEmbedding

/-- Full graph embeddings preserve closed occurrences by composition.
The proof uses closedness first at the host-embedding level and
then at the source-occurrence level. -/
def comp
    {A : SimpleGraph U} {B : SimpleGraph V} {C : SimpleGraph W}
    (f : ClosedGraphEmbedding B C) (g : ClosedGraphEmbedding A B) :
    ClosedGraphEmbedding A C where
  toEmbedding := g.toEmbedding.trans f.toEmbedding
  induced := by
    intro u v
    exact (f.induced (g.toEmbedding u) (g.toEmbedding v)).trans
      (g.induced u v)
  closed := by
    intro x y z hx hy hxy hxz hyz
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    have hInHost : z ∈ Set.range f.toEmbedding :=
      f.closed ⟨g.toEmbedding u, rfl⟩
        ⟨g.toEmbedding v, rfl⟩ hxy hxz hyz
    obtain ⟨w, rfl⟩ := hInHost
    have huAdj : B.Adj (g.toEmbedding u) w :=
      (f.induced (g.toEmbedding u) w).mp hxz
    have hvAdj : B.Adj (g.toEmbedding v) w :=
      (f.induced (g.toEmbedding v) w).mp hyz
    have hne : g.toEmbedding u ≠ g.toEmbedding v := by
      intro heq
      apply hxy
      exact congrArg f.toEmbedding heq
    obtain ⟨t, rfl⟩ :=
      g.closed ⟨u, rfl⟩ ⟨v, rfl⟩ hne huAdj hvAdj
    exact ⟨t, rfl⟩

/-- Identity embeddings preserve the entire graph and its midpoint
closure, and hence define identity maps on closed occurrences. -/
def id (A : SimpleGraph U) : ClosedGraphEmbedding A A where
  toEmbedding := Function.Embedding.refl U
  induced := by
    intro u v
    rfl
  closed := by
    intro x y z hx hy hne hxz hyz
    exact ⟨z, rfl⟩

/-- Coordinate maps on occurrence vertices commute strictly with
composition. This is the coordinate-level naturality needed for
reifying copies by unary functions in a closure expansion. -/
theorem comp_apply
    {A : SimpleGraph U} {B : SimpleGraph V} {C : SimpleGraph W}
    (f : ClosedGraphEmbedding B C) (g : ClosedGraphEmbedding A B)
    (u : U) :
    (f.comp g).toEmbedding u = f.toEmbedding (g.toEmbedding u) :=
  rfl

end ClosedGraphEmbedding

/-- Intrinsic indexed occurrence type: *all* closed induced A-copies
in a host G, rather than only those selected during the recursion. -/
abbrev ClosedGraphOccurrence
    (A : SimpleGraph U) (G : SimpleGraph V) :=
  ClosedGraphEmbedding A G

/-- Every closed host embedding acts canonically on the full
occurrence type, including copies created at earlier gluing steps. -/
def mapClosedOccurrence
    {A : SimpleGraph U} {B : SimpleGraph V} {C : SimpleGraph W}
    (f : ClosedGraphEmbedding B C) :
    ClosedGraphOccurrence A B → ClosedGraphOccurrence A C :=
  fun a => f.comp a

end CoherentPort
end StructuralRamsey.Girth
