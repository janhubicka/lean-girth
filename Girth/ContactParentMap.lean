import Girth.ContactTrainData
import Girth.ContactBadCycle

/-! Maps between actual train cuts and basic inherited carrier facts. -/
namespace StructuralRamsey.Girth
universe v
variable {V E I : Type v}

namespace ContactTrainData
variable {m : ℕ} (T : ContactTrainData E m)

/-- The actual parent map between two cuts is well defined by
surjectivity of the finer parent and nesting. -/
noncomputable def parentMap (μ ν : Fin (m+1)) (_hle : μ ≤ ν)
    (p : T.Wagon μ) : T.Wagon ν :=
  T.parent ν (Classical.choose (T.surj μ p))

theorem parentMap_parent (μ ν : Fin (m+1)) (hle : μ ≤ ν) (e : E) :
    T.parentMap μ ν hle (T.parent μ e) = T.parent ν e :=
  T.nested μ ν hle _ e (Classical.choose_spec (T.surj μ (T.parent μ e)))

end ContactTrainData

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)
variable {m : ℕ} (T : ContactTrainData E m)

theorem wagon_parent_subset (μ ν : Fin (m+1)) (hle : μ ≤ ν) (p : T.Wagon μ) :
    (D.atCut (T.parent μ)).contactWagonCarrier p ⊆
      (D.atCut (T.parent ν)).contactWagonCarrier (T.parentMap μ ν hle p) := by
  rintro x ⟨e,he,hx⟩
  refine ⟨e,?_,hx⟩
  rw [← he,T.parentMap_parent]

theorem top_wagonGirth (g : ℕ) :
    LabelledGirthGT (D.atCut (T.parent ⟨m,by omega⟩)).contactWagonCarrier g := by
  rintro ⟨C,_⟩
  let i : Fin C.length := ⟨0,by have := C.hlength; omega⟩
  obtain ⟨e,he⟩ := T.surj _ (C.label i)
  obtain ⟨f,hf⟩ := T.surj _ (C.label (cyclicSucc i))
  have heq := he.symm.trans ((T.top e f).trans hf)
  exact contactSucc_ne C.hlength i (C.label_injective heq).symm

end ContactHypergraphData

end StructuralRamsey.Girth
