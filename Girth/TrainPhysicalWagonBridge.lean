import Girth.TrainWagonSharedEdgeContact

/-!
# Genuine core-edge bridges from shared wagon contacts

A standard-picture wagon U can be tagged by a core wagon X only when
some actual subsystem edge s has both ancestors. The same shared edge
then connects every standard-picture edge of U to a physical core
edge of X: first move inside U to s, then use equality of the
standard and core images of s.

This discharges the essential per-standard-picture instance of the
shared-label bridge hypothesis in the physical edge normal-form proof,
without inventing any contact from equal vertex carriers.
-/

namespace StructuralRamsey.Girth

universe u v w
variable {I : Type u} {Shared : Type v}
variable {OldWagon CoreWagon OldEdge CoreEdge E : Type w}

/-- A contact tagged by an actual gluing edge provides a real
core representative, reached through one old-wagon relation step. -/
theorem sharedWagonContact_has_physicalBridge
    (old : I → Shared → OldWagon)
    (core : I → Shared → CoreWagon)
    (hPreserve : ∀ i s t,
      old i s = old i t → core i s = core i t)
    (std : I → OldEdge → E)
    (coreEmbed : CoreEdge → E)
    (sharedOld : I → Shared → OldEdge)
    (sharedCore : I → Shared → CoreEdge)
    (oldClass : OldEdge → OldWagon)
    (coreClass : CoreEdge → CoreWagon)
    (hOldClass : ∀ i s, oldClass (sharedOld i s) = old i s)
    (hCoreClass : ∀ i s, coreClass (sharedCore i s) = core i s)
    (hGlue : ∀ i s, std i (sharedOld i s) =
      coreEmbed (sharedCore i s))
    (R : E → E → Prop)
    (hStandard : ∀ i a b,
      oldClass a = oldClass b → R (std i a) (std i b))
    (i : I) (a : OldEdge) (c : CoreWagon)
    (hContact :
      wagonContactGlue (wagonSharedEdgeContact old core)
        i (oldClass a) = some c) :
    ∃ b : CoreEdge,
      coreClass b = c ∧ R (std i a) (coreEmbed b) := by
  have hUnique : ∀ j d x y,
      wagonSharedEdgeContact old core j d x →
      wagonSharedEdgeContact old core j d y → x = y := by
    intro j d x y hx hy
    exact wagonSharedEdgeContact_unique old core hPreserve
      j d x y hx hy
  have hActual :
      wagonSharedEdgeContact old core i (oldClass a) c :=
    (wagonContactGlue_eq_some_iff
      (wagonSharedEdgeContact old core)
      hUnique i (oldClass a) c).mp hContact
  rcases hActual with ⟨s, hos, hcs⟩
  refine ⟨sharedCore i s, ?_, ?_⟩
  · exact (hCoreClass i s).trans hcs
  · have hSame : oldClass a = oldClass (sharedOld i s) :=
      hos.symm.trans (hOldClass i s).symm
    have hStep := hStandard i a (sharedOld i s) hSame
    simpa only [hGlue i s] using hStep

end StructuralRamsey.Girth
