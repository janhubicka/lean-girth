import Girth.ForestObservableProfile
import Mathlib.Tactic

/-!
# Semantic contraction of a fixed marked configuration

Equal kernels of two marked-vertex maps give the unique label-preserving
bijection of their realised unions. These bijections compose exactly and
preserve equality and containment of every named A/B carrier whose vertex
positions are retained. Thus pure transport chains have a coherent semantic
contraction, without any bound on their length.

This is not a free-ancestral shape map. Nor does a marked kernel record
contacts with unmarked ambient edges; boundary extension tests need more data.
-/

namespace StructuralRamsey.Girth

universe u v w z

/-- Equality of all coincidences between retained vertex positions. -/
def SameMarkedKernel {I : Type u} {W : Type v} {Z : Type w}
    (f : I → W) (g : I → Z) : Prop :=
  ∀ i j, f i = f j ↔ g i = g j

namespace SameMarkedKernel

variable {I : Type u} {W : Type v} {Z : Type w} {Y : Type z}
    {f : I → W} {g : I → Z} {k : I → Y}

protected theorem refl (f : I → W) : SameMarkedKernel f f :=
  fun _ _ => Iff.rfl

protected theorem symm (h : SameMarkedKernel f g) : SameMarkedKernel g f :=
  fun i j => (h i j).symm

protected theorem trans (h : SameMarkedKernel f g)
    (h' : SameMarkedKernel g k) : SameMarkedKernel f k :=
  fun i j => (h i j).trans (h' i j)

/-- A single injective transport of the entire marked union is neutral. -/
theorem of_injective (f : I → W) (e : W → Z)
    (he : Function.Injective e) : SameMarkedKernel f (e ∘ f) := by
  intro i j
  exact ⟨fun hij => congrArg e hij, fun hij => he hij⟩

/-- Containment of named carriers is determined by the marked kernel. -/
theorem image_subset_iff (h : SameMarkedKernel f g) (S T : Set I) :
    f '' S ⊆ f '' T ↔ g '' S ⊆ g '' T := by
  constructor
  · intro hSub y hy
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨j, hj, hji⟩ := hSub ⟨i, hi, rfl⟩
    exact ⟨j, hj, (h j i).mp hji⟩
  · intro hSub y hy
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨j, hj, hji⟩ := hSub ⟨i, hi, rfl⟩
    exact ⟨j, hj, (h j i).mpr hji⟩

/-- In particular, semantic contraction cannot identify distinct named
physical carriers if all their vertex positions have been retained. -/
theorem image_eq_iff (h : SameMarkedKernel f g) (S T : Set I) :
    f '' S = f '' T ↔ g '' S = g '' T := by
  constructor
  · intro heq
    apply Set.Subset.antisymm
    · exact (h.image_subset_iff S T).mp heq.subset
    · exact (h.image_subset_iff T S).mp heq.symm.subset
  · intro heq
    apply Set.Subset.antisymm
    · exact (h.image_subset_iff S T).mpr heq.subset
    · exact (h.image_subset_iff T S).mpr heq.symm.subset

theorem carrier_injective_iff {C : Type*}
    (h : SameMarkedKernel f g) (carrier : C → Set I) :
    Function.Injective (fun c => f '' carrier c) ↔
      Function.Injective (fun c => g '' carrier c) := by
  constructor
  · intro hInj c d hEq
    exact hInj ((h.image_eq_iff (carrier c) (carrier d)).mpr hEq)
  · intro hInj c d hEq
    exact hInj ((h.image_eq_iff (carrier c) (carrier d)).mp hEq)

end SameMarkedKernel

/-- A point in a realised marked union is transported by any label naming
it. Kernel equality below proves independence of this choice. -/
noncomputable def markedRangeMap {I : Type u} {W : Type v} {Z : Type w}
    (f : I → W) (g : I → Z) : Set.range f → Set.range g :=
  fun x => ⟨g (Classical.choose x.property),
    ⟨Classical.choose x.property, rfl⟩⟩

@[simp] theorem markedRangeMap_mk {I : Type u} {W : Type v} {Z : Type w}
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g) (i : I) :
    markedRangeMap f g ⟨f i, ⟨i, rfl⟩⟩ = ⟨g i, ⟨i, rfl⟩⟩ := by
  apply Subtype.ext
  exact (h _ i).mp (Classical.choose_spec (show f i ∈ Set.range f from ⟨i, rfl⟩))

/-- The semantic transport exists on the realised union, not necessarily
on the whole ambient host. No ambient cardinality assumption is needed. -/
noncomputable def markedRangeEquiv {I : Type u} {W : Type v} {Z : Type w}
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g) :
    Set.range f ≃ Set.range g := by
  apply Equiv.ofBijective (markedRangeMap f g)
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hLabel : g (Classical.choose x.property) =
        g (Classical.choose y.property) := congrArg Subtype.val hxy
    exact (Classical.choose_spec x.property).symm.trans
      (((h _ _).mpr hLabel).trans (Classical.choose_spec y.property))
  · intro y
    obtain ⟨i, hi⟩ := y.property
    refine ⟨⟨f i, ⟨i, rfl⟩⟩, ?_⟩
    rw [markedRangeMap_mk f g h i]
    exact Subtype.ext hi

@[simp] theorem markedRangeEquiv_mk {I : Type u} {W : Type v} {Z : Type w}
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g) (i : I) :
    markedRangeEquiv f g h ⟨f i, ⟨i, rfl⟩⟩ = ⟨g i, ⟨i, rfl⟩⟩ :=
  markedRangeMap_mk f g h i

/-- There is no choice of mutually incompatible transports once every
retained vertex label is required to commute. -/
theorem markedRangeEquiv_unique {I : Type u} {W : Type v} {Z : Type w}
    (f : I → W) (g : I → Z) (h : SameMarkedKernel f g)
    (T : Set.range f ≃ Set.range g)
    (hT : ∀ i, T ⟨f i, ⟨i, rfl⟩⟩ = ⟨g i, ⟨i, rfl⟩⟩) :
    T = markedRangeEquiv f g h := by
  apply Equiv.ext
  intro x
  obtain ⟨i, hi⟩ := x.property
  have hx : x = (⟨f i, ⟨i, rfl⟩⟩ : Set.range f) := Subtype.ext hi.symm
  rw [hx, hT i, markedRangeEquiv_mk]

/-- Contraction of successive neutral intervals agrees with direct
contraction. This is the coherence needed for pure transport chains. -/
theorem markedRangeEquiv_trans {I : Type u} {W : Type v} {Z : Type w}
    {Y : Type z} (f : I → W) (g : I → Z) (k : I → Y)
    (hfg : SameMarkedKernel f g) (hgk : SameMarkedKernel g k) :
    (markedRangeEquiv f g hfg).trans (markedRangeEquiv g k hgk) =
      markedRangeEquiv f k (hfg.trans hgk) := by
  apply markedRangeEquiv_unique f k (hfg.trans hgk)
  intro i
  change markedRangeEquiv g k hgk
    (markedRangeEquiv f g hfg ⟨f i, ⟨i, rfl⟩⟩) = ⟨k i, ⟨i, rfl⟩⟩
  rw [markedRangeEquiv_mk, markedRangeEquiv_mk]

/-- Retained old-front ports are fixed pointwise when their labels are. -/
theorem markedRangeEquiv_fixed {I : Type u} {W : Type v}
    (f g : I → W) (h : SameMarkedKernel f g) (i : I)
    (hi : f i = g i) :
    (markedRangeEquiv f g h ⟨f i, ⟨i, rfl⟩⟩).val = f i := by
  rw [markedRangeEquiv_mk]
  exact hi.symm

/-- The existing Boolean observable profile supplies the kernel hypothesis.
This does not upgrade the semantic bijection to a successor shape map. -/
theorem sameMarkedKernel_of_observableProfile_eq
    (q : ℕ) {VB : Type u} {Role : Type*} {W : Type v} {Z : Type w}
    [DecidableEq W] [DecidableEq Z]
    (f : MarkedCopyVertex q VB → W) (g : MarkedCopyVertex q VB → Z)
    (role : MarkedCopyVertex q VB → Role)
    (h : forestObservableProfile q f role = forestObservableProfile q g role) :
    SameMarkedKernel f g := by
  intro i j
  have hb := congrFun (congrFun (congrArg Prod.fst h) i) j
  change decide (f i = f j) = decide (g i = g j) at hb
  constructor
  · intro hf
    by_contra hg
    simp [hf, hg] at hb
  · intro hg
    by_contra hf
    simp [hf, hg] at hb

end StructuralRamsey.Girth
