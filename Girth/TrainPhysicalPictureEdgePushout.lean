import Girth.TrainPictureWagonFromSharedEdges

/-!
# Canonical physical edge pushout for one picture step

At the one-cut edge level, actual shared old edges are represented
by their core image. Every other old edge is private to its
standard-picture index. The resulting physical edge type is a
shared core plus the private old edges for each index, not a
disjoint union of all whole standard copies.

The core and standard edge maps cover this type, and the standard
map sends each genuine shared old edge to its prescribed core edge.
The shared/private wagon tag consequently has the correct restriction
to every standard picture, provided shared wagon classes preserve
and reflect equality on the gluing edge subsystem.

Under these conditions the verified explicit-generator and real
core-edge bridge theorem yields the COMPLETE one-cut edge-equivalence
normal form for this concrete physical edge pushout. It does not
yet transfer allowed-part parameters or system-Girth A1--A3.
-/

namespace StructuralRamsey.Girth

universe v
variable {I Shared OldEdge CoreEdge Old Core : Type v}

/-- The physical edge set of a free simultaneous picture attachment:
all core edges, and one PRIVATE copy of each old non-shared edge
for every standard-copy index. -/
abbrev PhysicalPictureEdge
    (inOld : Shared ↪ OldEdge)
    (I CoreEdge : Type v) :=
  CoreEdge ⊕ (I × {a : OldEdge // a ∉ Set.range inOld})

/-- Embed an actual core edge into the physical pushout. -/
def physicalCoreEdge
    (inOld : Shared ↪ OldEdge)
    (I : Type v) (b : CoreEdge) :
    PhysicalPictureEdge inOld I CoreEdge :=
  Sum.inl b

/-- An old edge belongs to the core when it is genuinely shared;
otherwise it is private to its standard-picture index. -/
noncomputable def physicalStandardEdge
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (i : I) (a : OldEdge) :
    PhysicalPictureEdge inOld I CoreEdge := by
  classical
  exact if h : a ∈ Set.range inOld then
    Sum.inl (inCore i (Classical.choose h))
  else
    Sum.inr (i, ⟨a, h⟩)

/-- Actual shared old edges are physically identified with their
specified core edge, rather than merely given equivalent labels. -/
theorem physicalStandardEdge_shared
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (i : I) (s : Shared) :
    physicalStandardEdge inOld inCore i (inOld s) =
      Sum.inl (inCore i s) := by
  classical
  unfold physicalStandardEdge
  split_ifs with h
  · have hs : Classical.choose h = s :=
      inOld.injective (Classical.choose_spec h)
    simp [hs]
  · exact False.elim (h ⟨s, rfl⟩)

/-- Every old edge not in the shared edge image has a truly
private occurrence in each standard picture. -/
theorem physicalStandardEdge_private
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (i : I) (a : OldEdge)
    (h : a ∉ Set.range inOld) :
    physicalStandardEdge inOld inCore i a =
      Sum.inr (i, (⟨a, h⟩ :
        {a : OldEdge // a ∉ Set.range inOld})) := by
  classical
  simp [physicalStandardEdge, h]

/-- The core edges and standard-picture edge maps cover EVERY
physical edge of the explicit free edge pushout. -/
theorem physicalPictureEdge_covered
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge) :
    ∀ e : PhysicalPictureEdge inOld I CoreEdge,
      (∃ b : CoreEdge, e = physicalCoreEdge inOld I b) ∨
        ∃ i : I, ∃ a : OldEdge,
          e = physicalStandardEdge inOld inCore i a := by
  intro e
  cases e with
  | inl b =>
      exact Or.inl ⟨b, rfl⟩
  | inr z =>
      rcases z with ⟨i, a⟩
      refine Or.inr ⟨i, a.1, ?_⟩
      simpa [physicalCoreEdge] using
        (physicalStandardEdge_private inOld inCore i a.1 a.2).symm

/-- The wagon tag of a physical edge. Core edges carry their core
wagon; a private old edge carries either its genuinely contacted
core wagon or a private (standard index, old wagon) label. -/
def physicalPictureWagonTag
    (inOld : Shared ↪ OldEdge)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (glue : I → Old → Option Core) :
    PhysicalPictureEdge inOld I CoreEdge → Core ⊕ (I × Old)
  | .inl b => Sum.inl (coreClass b)
  | .inr z => gluedStandardNode glue z.1 (oldClass z.2.1)

/-- The physical standard edge map preserves its old-wagon
ancestor tag. For shared old edges this follows from the ACTUAL
gluing-edge-to-core-wagon compatibility, not carrier equality. -/
theorem physicalStandardEdge_tag
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (glue : I → Old → Option Core)
    (hContact : ∀ i s,
      glue i (oldClass (inOld s)) =
        some (coreClass (inCore i s)))
    (i : I) (a : OldEdge) :
    physicalPictureWagonTag inOld coreClass oldClass glue
        (physicalStandardEdge inOld inCore i a) =
      gluedStandardNode glue i (oldClass a) := by
  classical
  by_cases h : a ∈ Set.range inOld
  · obtain ⟨s, hs⟩ := h
    subst a
    rw [physicalStandardEdge_shared inOld inCore i s]
    change Sum.inl (coreClass (inCore i s)) =
      gluedStandardNode glue i (oldClass (inOld s))
    simp [gluedStandardNode, hContact i s]
  · rw [physicalStandardEdge_private inOld inCore i a h]
    rfl

/-- The core wagon labels agree with the explicit physical tags. -/
theorem physicalCoreEdge_tag
    (inOld : Shared ↪ OldEdge)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (glue : I → Old → Option Core)
    (b : CoreEdge) :
    physicalPictureWagonTag inOld coreClass oldClass glue
      (physicalCoreEdge inOld I b) =
      Sum.inl (coreClass b) := rfl

/-- In the genuine free edge pushout, explicit core/standard
wagon generators produce EXACTLY the shared/private label
equivalence. No generator-safety, private-fibre, core-fibre,
or ghost-contact hypothesis remains. -/
theorem physicalPictureGenerated_iff_tag
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (hPreserve : ∀ i s t,
      oldClass (inOld s) = oldClass (inOld t) →
        coreClass (inCore i s) = coreClass (inCore i t)) :
    let oldShared : I → Shared → Old :=
      fun _ s => oldClass (inOld s)
    let coreShared : I → Shared → Core :=
      fun i s => coreClass (inCore i s)
    let glue := wagonContactGlue
      (wagonSharedEdgeContact oldShared coreShared)
    let tag := physicalPictureWagonTag inOld
      coreClass oldClass glue
    ∀ e f : PhysicalPictureEdge inOld I CoreEdge,
      TrainEdgeGenerated
        (PictureWagonStep
          (physicalCoreEdge inOld I)
          (physicalStandardEdge inOld inCore)
          coreClass oldClass) e f ↔
        tag e = tag f := by
  dsimp
  let oldShared : I → Shared → Old :=
    fun _ s => oldClass (inOld s)
  let coreShared : I → Shared → Core :=
    fun i s => coreClass (inCore i s)
  let glue : I → Old → Option Core :=
    wagonContactGlue (wagonSharedEdgeContact oldShared coreShared)
  have hUnique : ∀ i a c d,
      wagonSharedEdgeContact oldShared coreShared i a c →
      wagonSharedEdgeContact oldShared coreShared i a d →
      c = d := by
    intro i a c d hc hd
    exact wagonSharedEdgeContact_unique oldShared coreShared
      hPreserve i a c d hc hd
  have hSharedTag : ∀ i s,
      glue i (oldClass (inOld s)) =
        some (coreClass (inCore i s)) := by
    intro i s
    apply (wagonContactGlue_eq_some_iff
      (wagonSharedEdgeContact oldShared coreShared) hUnique
        i (oldClass (inOld s))
          (coreClass (inCore i s))).mpr
    exact ⟨s, rfl, rfl⟩
  exact pictureWagonGenerated_iff_sameTag_of_sharedEdges
    (physicalCoreEdge inOld I)
    (physicalStandardEdge inOld inCore)
    coreClass oldClass oldShared coreShared hPreserve
    (fun _ s => inOld s)
    (fun i s => inCore i s)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun i s => physicalStandardEdge_shared inOld inCore i s)
    (physicalPictureWagonTag inOld coreClass oldClass glue)
    (physicalCoreEdge_tag inOld coreClass oldClass glue)
    (physicalStandardEdge_tag inOld inCore coreClass oldClass
      glue hSharedTag)
    (physicalPictureEdge_covered inOld inCore)

end StructuralRamsey.Girth
