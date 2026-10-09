import Girth.ForestArbitraryPortPushout
import Mathlib.Tactic

/-!
# Universal property of the explicit one-port B-piece pushout

The vertex set Old ⊕ (New \ NewPort) is more than a convenient model:
it has the universal mapping property for gluing the two sides
over the chosen port isomorphism.

Given maps f:Old→T and g:New→T agreeing on identified port vertices,
there is exactly one map out of the glued vertex set that restricts
to f and g under its two canonical embeddings. No injectivity is
required for target maps.

This produces a coherent ONE-STEP evaluation interface for a
fixed port-gluing record. It does not give a global, simultaneous
evaluation of all successor histories or prove that Ramsey shape
reductions preserve a prescribed geometry.
-/

namespace StructuralRamsey.Girth

universe v w

namespace PortGluing

variable {Old New : Type v}

/-- A compatible pair of evaluations agrees exactly on the chosen
new-to-old port isomorphism. -/
def PortCompatible (G : PortGluing Old New) {T : Type w}
    (oldMap : Old → T) (newMap : New → T) : Prop :=
  ∀ (y : New) (hy : y ∈ G.newPort),
    oldMap (G.identify ⟨y, hy⟩).1 = newMap y

/-- The unique possible extension off the port: on old vertices
use f, and on private new vertices use g. -/
def lift (G : PortGluing Old New) {T : Type w}
    (oldMap : Old → T) (newMap : New → T) :
    G.Vertex → T
  | .inl x => oldMap x
  | .inr y => newMap y.1

@[simp] theorem lift_old (G : PortGluing Old New)
    {T : Type w} (oldMap : Old → T) (newMap : New → T)
    (x : Old) :
    G.lift oldMap newMap (G.oldEmbedding x) = oldMap x := rfl

/-- The extension agrees with g on ALL new vertices, including
those identified with the old port, precisely when the maps are
compatible on the prescribed separator. -/
theorem lift_new (G : PortGluing Old New)
    {T : Type w} (oldMap : Old → T) (newMap : New → T)
    (hComp : G.PortCompatible oldMap newMap)
    (y : New) :
    G.lift oldMap newMap (G.newEmbedding y) = newMap y := by
  classical
  by_cases hy : y ∈ G.newPort
  · rw [G.newEmbedding_apply_of_mem y hy]
    exact hComp y hy
  · rw [G.newEmbedding_apply_of_not_mem y hy]
    rfl

/-- Conversely, any map respecting the two canonical embeddings
necessarily witnesses the port compatibility condition. -/
theorem portCompatible_of_factor
    (G : PortGluing Old New)
    {T : Type w} (oldMap : Old → T) (newMap : New → T)
    (f : G.Vertex → T)
    (hOld : ∀ x, f (G.oldEmbedding x) = oldMap x)
    (hNew : ∀ y, f (G.newEmbedding y) = newMap y) :
    G.PortCompatible oldMap newMap := by
  intro y hy
  calc
    oldMap (G.identify ⟨y, hy⟩).1 =
        f (G.oldEmbedding (G.identify ⟨y, hy⟩).1) :=
      (hOld _).symm
    _ = f (G.newEmbedding y) := by rw [G.agree_on_port hy]
    _ = newMap y := hNew y

/-- Every vertex of the explicit pushout lies in one canonical
old or new image. This includes private vertices, not only ports. -/
theorem old_new_images_cover (G : PortGluing Old New) :
    ∀ z : G.Vertex,
      (∃ x : Old, G.oldEmbedding x = z) ∨
      (∃ y : New, G.newEmbedding y = z) := by
  classical
  intro z
  cases z with
  | inl x =>
      exact Or.inl ⟨x, rfl⟩
  | inr y =>
      right
      refine ⟨y.1, ?_⟩
      rw [G.newEmbedding_apply_of_not_mem y.1 y.2]

/-- No other function can be an extension of the two prescribed
side maps. This is uniqueness in the universal property. -/
theorem lift_unique (G : PortGluing Old New)
    {T : Type w} (oldMap : Old → T) (newMap : New → T)
    (f : G.Vertex → T)
    (hOld : ∀ x, f (G.oldEmbedding x) = oldMap x)
    (hNew : ∀ y, f (G.newEmbedding y) = newMap y) :
    f = G.lift oldMap newMap := by
  funext z
  obtain ⟨x, hx⟩ | ⟨y, hy⟩ := G.old_new_images_cover z
  · rw [← hx, hOld, G.lift_old]
  · rw [← hy, hNew]
    exact (G.lift_new oldMap newMap
      (G.portCompatible_of_factor oldMap newMap f hOld hNew) y).symm

/-- Full set-theoretic pushout property: compatible side maps
extend, and the extension is uniquely determined by both sides.
This is the correct fixed-gluing evaluation theorem for a single
B-piece birth. -/
theorem existsUnique_lift (G : PortGluing Old New)
    {T : Type w} (oldMap : Old → T) (newMap : New → T)
    (hComp : G.PortCompatible oldMap newMap) :
    ∃! f : G.Vertex → T,
      (∀ x, f (G.oldEmbedding x) = oldMap x) ∧
      (∀ y, f (G.newEmbedding y) = newMap y) := by
  refine ⟨G.lift oldMap newMap, ?_, ?_⟩
  · exact ⟨G.lift_old oldMap newMap,
      G.lift_new oldMap newMap hComp⟩
  · intro f hf
    exact G.lift_unique oldMap newMap f hf.1 hf.2

end PortGluing

end StructuralRamsey.Girth
