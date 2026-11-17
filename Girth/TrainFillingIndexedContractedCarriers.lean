import Girth.TrainFillingIndexedCarrierGeometry
import Girth.TrainFillingSelectedEdgeRange

set_option Elab.async false

/-! # Selected images of whole contracted carriers -/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Y : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- The actual selected M-copy vertex embedding alone constructs the
corresponding physical old-edge embedding, once it maps each whole
contracted source carrier onto an old N-edge. No independent physical
edge map, carrier equality, or injectivity are supplied. -/
def contractedOldEdgeEmbedding
    [Nontrivial X]
    (hOld : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (F : UniformFillingData Y X)
    (vertex : Vertex U ↪ Y)
    (hImage : ∀ e : C × P,
      vertex '' contractedCarrier U e ∈ F.oldEdges) :
    (C × P) ↪ F.OldEdge :=
  F.oldEdgeEmbedding_of_exact_carriers (contractedCarrier U)
    (contractedCarrier_injective U hOld) vertex
    (fun e => (⟨vertex '' contractedCarrier U e, hImage e⟩ : F.OldEdge))
    (fun _ => rfl)

/-- Every constructed contracted old edge is literally the image of
its full first-wagon carrier under the selected vertex embedding. -/
@[simp] theorem contractedOldEdgeEmbedding_carrier
    [Nontrivial X]
    (hOld : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (F : UniformFillingData Y X)
    (vertex : Vertex U ↪ Y)
    (hImage : ∀ e : C × P,
      vertex '' contractedCarrier U e ∈ F.oldEdges)
    (e : C × P) :
    (contractedOldEdgeEmbedding U hOld F vertex hImage e).1 =
      vertex '' contractedCarrier U e := rfl

end StructuralRamsey.Girth.IndexedPrivateChoice
