import Girth.TrainWagonSharedEdgeContact
import Girth.TrainWagonClassRestriction

/-!
# Genuine shared-edge wagon ancestor quotients and parent maps

At each level, a train's wagon ancestors are quotient classes of
PHYSICAL edge labels, not merely declared abstract nodes. Given
shared-edge embeddings into an old standard picture and a witness
core, the preservation-and-reflection hypothesis on the shared
subsystem yields equivalence of their actual quotient label equality.

We derive a canonical partial-injective core contact and show that
nesting of train levels gives the required parent compatibility.

This verifies the actual shared-edge QUOTIENT interface. It does not
yet identify the full generated equivalence on the entire picture
or preserve the acceptable-cycle predicates (A1)--(A3).
-/

namespace StructuralRamsey.Girth

universe v
variable {I Shared OldEdge CoreEdge : Type v}

/-- The canonical parent map between two horizontal wagon cuts is
well-defined by nesting of the train edge equivalences. -/
def EdgeTrainLevels.wagonParent
    {m : ℕ} (T : EdgeTrainLevels OldEdge m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν) :
    Quotient (T.wagonSetoid μ) → Quotient (T.wagonSetoid ν) :=
  fun q => Quotient.liftOn q
    (fun a => Quotient.mk (T.wagonSetoid ν) a)
    (by
      intro a b hab
      exact Quotient.sound (T.nested μ ν hμν a b hab))

@[simp]
theorem EdgeTrainLevels.wagonParent_mk
    {m : ℕ} (T : EdgeTrainLevels OldEdge m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν) (a : OldEdge) :
    T.wagonParent μ ν hμν (Quotient.mk (T.wagonSetoid μ) a) =
      Quotient.mk (T.wagonSetoid ν) a := rfl

/-- The old wagon label of a real gluing-subsystem edge. -/
def oldSharedWagonLabel
    {m : ℕ} (T : EdgeTrainLevels OldEdge m)
    (μ : Fin (m + 1)) (oldEmbed : I → Shared ↪ OldEdge)
    (i : I) (s : Shared) : Quotient (T.wagonSetoid μ) :=
  Quotient.mk (T.wagonSetoid μ) (oldEmbed i s)

/-- Equality of the actual old and core wagon quotient labels on
SHARED edges is equivalent, exactly by preservation/reflection of
the train embedding at this level. -/
theorem sharedWagonLabel_eq_iff
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ : Fin (m + 1))
    (oldEmbed : I → Shared ↪ OldEdge)
    (coreEmbed : I → Shared ↪ CoreEdge)
    (hReflectPreserve : ∀ i s t,
      Told.rel μ (oldEmbed i s) (oldEmbed i t) ↔
        Tcore.rel μ (coreEmbed i s) (coreEmbed i t))
    (i : I) (s t : Shared) :
    oldSharedWagonLabel Told μ oldEmbed i s =
      oldSharedWagonLabel Told μ oldEmbed i t ↔
    oldSharedWagonLabel Tcore μ coreEmbed i s =
      oldSharedWagonLabel Tcore μ coreEmbed i t := by
  constructor
  · intro h
    apply Quotient.sound
    exact (hReflectPreserve i s t).mp (Quotient.exact h)
  · intro h
    apply Quotient.sound
    exact (hReflectPreserve i s t).mpr (Quotient.exact h)

/-- A shared-subsystem train embedding gives the actual injectivity
of standard wagon ancestor tags in the glued representation. -/
theorem sharedWagonQuotient_glue_injective
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ : Fin (m + 1))
    (oldEmbed : I → Shared ↪ OldEdge)
    (coreEmbed : I → Shared ↪ CoreEdge)
    (hRel : ∀ i s t,
      Told.rel μ (oldEmbed i s) (oldEmbed i t) ↔
        Tcore.rel μ (coreEmbed i s) (coreEmbed i t))
    (i : I) :
    Function.Injective
      (gluedStandardNode
        (wagonContactGlue
          (wagonSharedEdgeContact
            (oldSharedWagonLabel Told μ oldEmbed)
            (oldSharedWagonLabel Tcore μ coreEmbed))) i) := by
  apply wagonSharedEdgeContact_glue_injective
    (oldSharedWagonLabel Told μ oldEmbed)
    (oldSharedWagonLabel Tcore μ coreEmbed)
  · intro j s t h
    exact (sharedWagonLabel_eq_iff
      Told Tcore μ oldEmbed coreEmbed hRel j s t).mp h
  · intro j s t h
    exact (sharedWagonLabel_eq_iff
      Told Tcore μ oldEmbed coreEmbed hRel j s t).mpr h

/-- The lower and upper quotient wagon ancestors commute with the
actual old/core shared-edge maps at every nested pair of levels. -/
theorem oldSharedWagonLabel_parent
    {m : ℕ} (T : EdgeTrainLevels OldEdge m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (embed : I → Shared ↪ OldEdge)
    (i : I) (s : Shared) :
    T.wagonParent μ ν hμν
      (oldSharedWagonLabel T μ embed i s) =
      oldSharedWagonLabel T ν embed i s := rfl

/-- Parent compatibility of ACTUAL quotient wagon contacts follows
from the train embedding preserving and reflecting the two levels.
Even a private child can have a shared core parent. -/
theorem sharedWagonQuotient_contact_parent
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (oldEmbed : I → Shared ↪ OldEdge)
    (coreEmbed : I → Shared ↪ CoreEdge)
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      Told.rel κ (oldEmbed i s) (oldEmbed i t) ↔
        Tcore.rel κ (coreEmbed i s) (coreEmbed i t))
    (i : I) (a : Quotient (Told.wagonSetoid μ))
    (c : Quotient (Tcore.wagonSetoid μ))
    (hContact :
      wagonContactGlue
          (wagonSharedEdgeContact
            (oldSharedWagonLabel Told μ oldEmbed)
            (oldSharedWagonLabel Tcore μ coreEmbed))
          i a = some c) :
    wagonContactGlue
        (wagonSharedEdgeContact
          (oldSharedWagonLabel Told ν oldEmbed)
          (oldSharedWagonLabel Tcore ν coreEmbed))
        i (Told.wagonParent μ ν hμν a) =
      some (Tcore.wagonParent μ ν hμν c) := by
  have hUniqueμ : ∀ j x c d,
      wagonSharedEdgeContact
        (oldSharedWagonLabel Told μ oldEmbed)
        (oldSharedWagonLabel Tcore μ coreEmbed)
        j x c →
      wagonSharedEdgeContact
        (oldSharedWagonLabel Told μ oldEmbed)
        (oldSharedWagonLabel Tcore μ coreEmbed)
        j x d → c = d := by
    intro j x c d hc hd
    exact wagonSharedEdgeContact_unique
      (oldSharedWagonLabel Told μ oldEmbed)
      (oldSharedWagonLabel Tcore μ coreEmbed)
      (fun k s t h =>
        (sharedWagonLabel_eq_iff
          Told Tcore μ oldEmbed coreEmbed (hRel μ) k s t).mp h)
      j x c d hc hd
  have hActual :=
    (wagonContactGlue_eq_some_iff
      (wagonSharedEdgeContact
        (oldSharedWagonLabel Told μ oldEmbed)
        (oldSharedWagonLabel Tcore μ coreEmbed))
      hUniqueμ i a c).mp hContact
  rcases hActual with ⟨s, hs, hc⟩
  have hParentActual :
      wagonSharedEdgeContact
        (oldSharedWagonLabel Told ν oldEmbed)
        (oldSharedWagonLabel Tcore ν coreEmbed)
        i (Told.wagonParent μ ν hμν a)
          (Tcore.wagonParent μ ν hμν c) := by
    refine ⟨s, ?_, ?_⟩
    · calc
        oldSharedWagonLabel Told ν oldEmbed i s =
          Told.wagonParent μ ν hμν
            (oldSharedWagonLabel Told μ oldEmbed i s) :=
          (oldSharedWagonLabel_parent Told μ ν hμν oldEmbed i s).symm
        _ = Told.wagonParent μ ν hμν a := congrArg _ hs
    · calc
        oldSharedWagonLabel Tcore ν coreEmbed i s =
          Tcore.wagonParent μ ν hμν
            (oldSharedWagonLabel Tcore μ coreEmbed i s) :=
          (oldSharedWagonLabel_parent Tcore μ ν hμν coreEmbed i s).symm
        _ = Tcore.wagonParent μ ν hμν c := congrArg _ hc
  have hUniqueν : ∀ j x c d,
      wagonSharedEdgeContact
        (oldSharedWagonLabel Told ν oldEmbed)
        (oldSharedWagonLabel Tcore ν coreEmbed)
        j x c →
      wagonSharedEdgeContact
        (oldSharedWagonLabel Told ν oldEmbed)
        (oldSharedWagonLabel Tcore ν coreEmbed)
        j x d → c = d := by
    intro j x c d hc hd
    exact wagonSharedEdgeContact_unique
      (oldSharedWagonLabel Told ν oldEmbed)
      (oldSharedWagonLabel Tcore ν coreEmbed)
      (fun k s t h =>
        (sharedWagonLabel_eq_iff
          Told Tcore ν oldEmbed coreEmbed (hRel ν) k s t).mp h)
      j x c d hc hd
  exact (wagonContactGlue_eq_some_iff
    (wagonSharedEdgeContact
      (oldSharedWagonLabel Told ν oldEmbed)
      (oldSharedWagonLabel Tcore ν coreEmbed))
    hUniqueν i _ _).mpr hParentActual

end StructuralRamsey.Girth
