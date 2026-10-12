import Girth.TrainPictureWagonGenerators

/-!
# Bottom equality and top universality of generated train wagons

The bottom train cut is equality because both the old and core
bottom wagon labels are injective on PHYSICAL edges.

For the TOP cut it is essential that every attached standard
picture contains at least one actual shared edge. Only then does
its universal old top wagon meet the universal core top wagon.
The connectedness of the generated top equivalence does NOT
follow merely from the separate universality of the old/core
relations. This matters when the recursion skips empty active
fibres.
-/

namespace StructuralRamsey.Girth

universe v
variable {E Core Old I CoreEdge OldEdge : Type v}

/-- At the bottom cut each basic core/standard wagon generator
already identifies equal physical edges; taking equivalence
closure therefore creates no new identifications. -/
theorem pictureWagonGenerated_bottom_eq
    (coreEmbed : CoreEdge → E)
    (std : I → OldEdge → E)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (hCoreInj : Function.Injective coreClass)
    (hOldInj : Function.Injective oldClass) :
    ∀ e f : E,
      TrainEdgeGenerated
        (PictureWagonStep coreEmbed std coreClass oldClass) e f ↔
      e = f := by
  let step := PictureWagonStep coreEmbed std coreClass oldClass
  have hBasic : ∀ e f, step e f → e = f := by
    intro e f h
    cases h with
    | core a b hab =>
        exact congrArg coreEmbed (hCoreInj hab)
    | standard i a b hab =>
        exact congrArg (std i) (hOldInj hab)
  intro e f
  constructor
  · intro h
    exact TrainEdgeGenerated.least
      step (fun x y => x = y)
      (fun _ => rfl)
      (fun _ _ hxy => hxy.symm)
      (fun _ _ _ hxy hyz => hxy.trans hyz)
      hBasic h
  · intro h
    subst f
    exact TrainEdgeGenerated.reflexive e

/-- A genuine shared physical edge in EVERY standard picture is
enough to join all old top wagons to the core top wagon. No
external shape-map or order argument is used. -/
theorem pictureWagonGenerated_top_universal
    (coreEmbed : CoreEdge → E)
    (std : I → OldEdge → E)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (hCoreUniversal : ∀ a b, coreClass a = coreClass b)
    (hOldUniversal : ∀ a b, oldClass a = oldClass b)
    (hCover : ∀ e : E,
      (∃ b, e = coreEmbed b) ∨ ∃ i a, e = std i a)
    (hShared : ∀ i : I,
      ∃ a : OldEdge, ∃ b : CoreEdge,
        std i a = coreEmbed b) :
    ∀ e f : E,
      TrainEdgeGenerated
        (PictureWagonStep coreEmbed std coreClass oldClass) e f := by
  let step := PictureWagonStep coreEmbed std coreClass oldClass
  have hReachCore : ∀ e : E,
      ∃ b : CoreEdge, TrainEdgeGenerated step e (coreEmbed b) := by
    intro e
    rcases hCover e with ⟨b, hb⟩ | ⟨i, a, he⟩
    · refine ⟨b, ?_⟩
      rw [hb]
      exact TrainEdgeGenerated.reflexive _
    · obtain ⟨d, b, hdb⟩ := hShared i
      refine ⟨b, ?_⟩
      rw [he]
      have hOld :
          TrainEdgeGenerated step (std i a) (std i d) :=
        TrainEdgeGenerated.basic _ _
          (PictureWagonStep.standard i a d (hOldUniversal a d))
      rw [hdb] at hOld
      exact hOld
  intro e f
  obtain ⟨a, hea⟩ := hReachCore e
  obtain ⟨b, hfb⟩ := hReachCore f
  have hab :
      TrainEdgeGenerated step (coreEmbed a) (coreEmbed b) :=
    TrainEdgeGenerated.basic _ _
      (PictureWagonStep.core a b (hCoreUniversal a b))
  exact TrainEdgeGenerated.transitive e (coreEmbed a) f hea
    (TrainEdgeGenerated.transitive (coreEmbed a) (coreEmbed b) f
      hab (TrainEdgeGenerated.symmetric f (coreEmbed b) hfb))

/-- A counterexample when the gluing subsystem has NO edge:
the old and core top cuts are each universal separately, but
their disjoint physical edges do not become equivalent. -/
theorem pictureWagonGenerated_top_noShared_counterexample :
    ¬ TrainEdgeGenerated
        (PictureWagonStep
          (fun (_ : Unit) => (0 : Fin 2))
          (fun (_ : Unit) (_ : Unit) => (1 : Fin 2))
          (fun (_ : Unit) => ())
          (fun (_ : Unit) => ()))
        (0 : Fin 2) (1 : Fin 2) := by
  intro h
  have hInjCore : Function.Injective (fun (_ : Unit) => ()) := by
    intro a b _
    exact Subsingleton.elim a b
  have hInjOld : Function.Injective (fun (_ : Unit) => ()) := by
    intro a b _
    exact Subsingleton.elim a b
  have heq : (0 : Fin 2) = (1 : Fin 2) :=
    (pictureWagonGenerated_bottom_eq
      (fun (_ : Unit) => (0 : Fin 2))
      (fun (_ : Unit) (_ : Unit) => (1 : Fin 2))
      (fun (_ : Unit) => ())
      (fun (_ : Unit) => ())
      hInjCore hInjOld 0 1).mp h
  exact (by decide : (0 : Fin 2) ≠ 1) heq

end StructuralRamsey.Girth
