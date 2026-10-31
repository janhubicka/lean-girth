import Girth.TrainFillingLengthTwo

/-!
# Filling preserves every old wagon carrier

At a fixed old cut, the filled parent is the old parent composed with
cover. Reuse the length-two module's general carrier and linearity facts;
no duplicate declaration and no system-girth inference from carriers.
-/

namespace StructuralRamsey.Girth.TrainFilling
universe v
variable {V I P : Type v}
variable (F : TrainFilling V) (copyCarrier : I → Set V)
variable (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P)
local notation "O" => F.oldData copyCarrier copyEdges parent
local notation "H" => F.filledData copyCarrier copyEdges parent

theorem wagonVertex_filled_iff_old (p : P) (x : V) :
    (H).WagonVertex p x ↔ (O).WagonVertex p x :=
  F.filled_wagonVertex_iff copyCarrier copyEdges parent p x

theorem wagonCarrier_filled_eq_old (p : P) :
    {x : V | (H).WagonVertex p x} =
      {x : V | (O).WagonVertex p x} := by
  ext x
  exact F.wagonVertex_filled_iff_old copyCarrier copyEdges parent p x
end StructuralRamsey.Girth.TrainFilling
