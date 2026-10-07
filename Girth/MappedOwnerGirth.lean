import Girth.OwnerGirth

/-! # Owner girth with a mapped local forest

The local witness forest lives in the core of the standard attachment, not
in the full attached picture.  At an owner change, the connector belongs to
the images of both local forest carriers under the injective core embedding.
We use cyclic owner compression in the whole picture and then pull the
incidence circuit back through the core embedding.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA X Y Z ι : Type v}

/-- A short support Berge cycle cannot be covered by standard copies if
constant owners contradict the old girth and changed owners connect through
a one-part local forest embedded in the whole picture. -/
theorem no_short_support_cycle_of_owner_mapped_forest
    (A : RelStructure L UA)
    (Old : RelStructure L X)
    (Whole : RelStructure L Z)
    [Fintype ι] [Nonempty ι]
    (standard : ι → RelStructure.Embedding Old Whole)
    {F : ι → HypergraphPiece Y}
    (hForest : ForestOfCopies F)
    (P : Set Y)
    (hPart : EdgesMeetPartAtMostOne F P)
    (core : Y ↪ Z)
    (g : ℕ)
    (hOld : GirthGT (supportCopies A Old) g)
    (c : BergeCycle (supportCopies A Whole))
    (hLen : c.length ≤ g)
    (owner : Fin c.length → ι)
    (hEdgeOwner :
      ∀ j, c.edge j ⊆ copyCarrier (standard (owner j)))
    (hBoundary :
      ∀ j, owner j ≠ owner (cyclicSucc j) →
        c.vertex j ∈
            core '' ((F (owner j)).restrictCarrier P).carrier ∧
          c.vertex j ∈
            core '' ((F (owner (cyclicSucc j))).restrictCarrier P).carrier) :
    False := by
  classical
  by_cases hConst : ∃ q : ι, ∀ j : Fin c.length, owner j = q
  · rcases hConst with ⟨q, hq⟩
    apply no_short_support_cycle_in_embedding
      A Old Whole (standard q) g hOld c hLen
    intro j
    simpa [hq j] using hEdgeOwner j
  · have hZero : 0 < c.length :=
      lt_of_lt_of_le (by decide) c.hlength
    let j0 : Fin c.length := ⟨0, hZero⟩
    have hNotAll : ¬ ∀ j : Fin c.length, owner j = owner j0 := by
      intro h
      exact hConst ⟨owner j0, h⟩
    push Not at hNotAll
    rcases hNotAll with ⟨j, hj⟩
    let raw :
        RawCyclicIncidenceData
          (fun i : ι => core '' ((F i).restrictCarrier P).carrier) :=
      RawCyclicIncidenceData.ofBergeCycle
        c owner (fun i => core '' ((F i).restrictCarrier P).carrier)
        hBoundary ⟨j, j0, hj⟩
    exact
      CyclicIncidenceData.no_cyclicIncidenceData_of_mapped_forest_part
        hForest P hPart core raw.compress

end StructuralRamsey.Girth
