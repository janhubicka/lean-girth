import Mathlib.Tactic

/-!
# Finite certificates for marked B-carrier contacts

For a fixed finite list of marked vertices, all old carriers have only
finitely many intersection masks.  Choose one representative old carrier
for each realised mask, without assuming that the old family is finite.

If a proposed fresh carrier meets old material only at marked vertices,
its intersection with each old carrier is determined by that carrier's
mask.  Thus any one-carrier overlap test depending only on the actual
intersection may be checked on the chosen finite representatives.

This does NOT preserve arbitrary running-intersection forests, does not
bound the ancestor levels of the representatives, and does not construct
a carrier-faithful successor-tree embedding.
-/

namespace StructuralRamsey.Girth

universe u v

variable {I : Type u} {W : Type v} [Fintype I]

/-- The intersection pattern of an ambient carrier on retained labelled
boundary vertices. Labels may coincide; no injectivity is required. -/
noncomputable def markedCarrierMask (f : I → W) (D : Set W) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => f i ∈ D)

@[simp] theorem mem_markedCarrierMask
    (f : I → W) (D : Set W) (i : I) :
    i ∈ markedCarrierMask f D ↔ f i ∈ D := by
  classical
  simp [markedCarrierMask]

/-- A mask is represented by some member of the old carrier family. -/
def MarkedCarrierMaskRealised
    (family : Set (Set W)) (f : I → W) (mask : Finset I) : Prop :=
  ∃ D ∈ family, markedCarrierMask f D = mask

/-- One representative per realised mask. Values on unrealised masks
are irrelevant, as only realised masks are indexed by the finite sample. -/
noncomputable def markedCarrierChoice
    (family : Set (Set W)) (f : I → W) (mask : Finset I) : Set W := by
  classical
  exact if h : MarkedCarrierMaskRealised family f mask
    then Classical.choose h
    else ∅

theorem markedCarrierChoice_mem
    (family : Set (Set W)) (f : I → W) (mask : Finset I)
    (h : MarkedCarrierMaskRealised family f mask) :
    markedCarrierChoice family f mask ∈ family := by
  simp only [markedCarrierChoice, dif_pos h]
  exact (Classical.choose_spec h).1

theorem markedCarrierChoice_mask
    (family : Set (Set W)) (f : I → W) (mask : Finset I)
    (h : MarkedCarrierMaskRealised family f mask) :
    markedCarrierMask f (markedCarrierChoice family f mask) = mask := by
  simp only [markedCarrierChoice, dif_pos h]
  exact (Classical.choose_spec h).2

/-- A finite family of actual old carriers covering every realised boundary
mask. It is not the original family, nor a subfamily of bounded history. -/
noncomputable def markedCarrierRepresentatives
    (family : Set (Set W)) (f : I → W) : Finset (Set W) := by
  classical
  exact
    (Finset.univ.filter
      (fun mask : Finset I => MarkedCarrierMaskRealised family f mask)).image
      (markedCarrierChoice family f)

theorem markedCarrierRepresentatives_subset
    (family : Set (Set W)) (f : I → W) :
    ∀ D ∈ markedCarrierRepresentatives family f, D ∈ family := by
  classical
  intro D hD
  obtain ⟨mask, hmask, hEq⟩ := Finset.mem_image.mp hD
  rw [← hEq]
  exact markedCarrierChoice_mem family f mask (Finset.mem_filter.mp hmask).2

theorem markedCarrierRepresentatives_cover
    (family : Set (Set W)) (f : I → W)
    (D : Set W) (hD : D ∈ family) :
    ∃ R ∈ markedCarrierRepresentatives family f,
      markedCarrierMask f R = markedCarrierMask f D := by
  classical
  let mask := markedCarrierMask f D
  have hReal : MarkedCarrierMaskRealised family f mask := ⟨D, hD, rfl⟩
  refine ⟨markedCarrierChoice family f mask, ?_,
    markedCarrierChoice_mask family f mask hReal⟩
  apply Finset.mem_image.mpr
  exact ⟨mask, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hReal⟩, rfl⟩

/-- There is at most one chosen representative per possible boundary mask.
This works even when the original old-carrier family is infinite. -/
theorem markedCarrierRepresentatives_card_le
    (family : Set (Set W)) (f : I → W) :
    (markedCarrierRepresentatives family f).card ≤
      Fintype.card (Finset I) := by
  classical
  let masks : Finset (Finset I) :=
    Finset.univ.filter (fun mask => MarkedCarrierMaskRealised family f mask)
  change (masks.image (markedCarrierChoice family f)).card ≤
    Fintype.card (Finset I)
  calc
    (masks.image (markedCarrierChoice family f)).card ≤ masks.card :=
      Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Finset I)).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card (Finset I) := Finset.card_univ

/-- Two old carriers with the same mask have the same intersection with
every boundary subset built from retained labelled vertices. -/
theorem markedCarrierMask_boundary_inter_eq
    (f : I → W) (D R : Set W) (S : Set I)
    (hMask : markedCarrierMask f D = markedCarrierMask f R) :
    (f '' S) ∩ D = (f '' S) ∩ R := by
  have hPoint (i : I) : f i ∈ D ↔ f i ∈ R := by
    constructor
    · intro hi
      have h : i ∈ markedCarrierMask f D :=
        (mem_markedCarrierMask f D i).mpr hi
      rw [hMask] at h
      exact (mem_markedCarrierMask f R i).mp h
    · intro hi
      have h : i ∈ markedCarrierMask f R :=
        (mem_markedCarrierMask f R i).mpr hi
      rw [← hMask] at h
      exact (mem_markedCarrierMask f D i).mp h
  apply Set.ext
  intro x
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hx⟩
    exact ⟨⟨i, hi, rfl⟩, (hPoint i).mp hx⟩
  · rintro ⟨⟨i, hi, rfl⟩, hx⟩
    exact ⟨⟨i, hi, rfl⟩, (hPoint i).mpr hx⟩

/-- If an attachment only contacts old carriers on marked ports,
equal masks produce literally equal overlaps with that attachment. -/
theorem freshCarrier_inter_eq_of_sameMask
    (family : Set (Set W)) (f : I → W) (S : Set I)
    (e D R : Set W)
    (hContact : ∀ F ∈ family, e ∩ F = (f '' S) ∩ F)
    (hD : D ∈ family) (hR : R ∈ family)
    (hMask : markedCarrierMask f D = markedCarrierMask f R) :
    e ∩ D = e ∩ R := by
  calc
    e ∩ D = (f '' S) ∩ D := hContact D hD
    _ = (f '' S) ∩ R :=
      markedCarrierMask_boundary_inter_eq f D R S hMask
    _ = e ∩ R := (hContact R hR).symm

/-- Exact finite test for a *single* new carrier against all old carriers.
The test predicate may require empty, singleton or A-edge intersections,
as long as it depends only on the actual intersection set.

This theorem does not imply that the combined designated carrier family
admits a join tree. -/
theorem freshCarrier_allContacts_iff_representatives
    (family : Set (Set W)) (f : I → W) (S : Set I)
    (e : Set W) (Allowed : Set W → Prop)
    (hContact : ∀ D ∈ family, e ∩ D = (f '' S) ∩ D) :
    (∀ D ∈ family, Allowed (e ∩ D)) ↔
      ∀ R ∈ markedCarrierRepresentatives family f, Allowed (e ∩ R) := by
  constructor
  · intro hAll R hR
    exact hAll R (markedCarrierRepresentatives_subset family f R hR)
  · intro hRep D hD
    obtain ⟨R, hR, hMask⟩ :=
      markedCarrierRepresentatives_cover family f D hD
    have hIn : R ∈ family :=
      markedCarrierRepresentatives_subset family f R hR
    have hEqual : e ∩ D = e ∩ R :=
      freshCarrier_inter_eq_of_sameMask family f S e D R
        hContact hD hIn hMask.symm
    rw [hEqual]
    exact hRep R hR

end StructuralRamsey.Girth
