import Girth.ContactTrainData

/-! Restrict train edge labels along an injection. Surviving
wagon labels are precisely the range of the original parents
on the retained edges, with their (possibly smaller) carriers.
Unused ambient vertices play no role in girth or parameters. -/

namespace StructuralRamsey.Girth
universe v
variable {V E F I : Type v}

namespace ContactTrainData
variable {m : ℕ} (T : ContactTrainData E m)

def pullTrain (f : F ↪ E) : ContactTrainData F m where
  Wagon := fun μ => Set.range (T.parent μ ∘ f)
  parent := fun μ e => ⟨T.parent μ (f e),⟨e,rfl⟩⟩
  surj := by
    intro μ p
    obtain ⟨e,he⟩ := p.property
    exact ⟨e,Subtype.ext he⟩
  nested := by
    intro μ ν h e g he
    exact Subtype.ext (T.nested μ ν h (f e) (f g) (congrArg Subtype.val he))
  bottom := by
    intro e g he
    exact f.injective (T.bottom (congrArg Subtype.val he))
  top := fun e g => Subtype.ext (T.top (f e) (f g))

theorem pullTrain_rel (f : F ↪ E) (μ : Fin (m+1)) (e g : F) :
    (T.pullTrain f).parent μ e = (T.pullTrain f).parent μ g ↔
      T.parent μ (f e) = T.parent μ (f g) :=
  ⟨fun he => congrArg Subtype.val he,fun he => by
    apply Subtype.ext
    exact he⟩

end ContactTrainData

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)
variable {m : ℕ} (T : ContactTrainData E m)

def pullEdges (f : F ↪ E) : ContactHypergraphData V F PEmpty.{v+1} where
  edgeCarrier := D.edgeCarrier ∘ f
  copyCarrier := PEmpty.elim
  copyEdges := PEmpty.elim

theorem pull_wagon_subset (f : F ↪ E) (μ : Fin (m+1))
    (p : (T.pullTrain f).Wagon μ) :
    ((D.pullEdges f).atCut ((T.pullTrain f).parent μ)).contactWagonCarrier p ⊆
      (D.atCut (T.parent μ)).contactWagonCarrier p.val := by
  rintro x ⟨e,he,hx⟩
  exact ⟨f e,congrArg Subtype.val he,hx⟩

theorem pull_wagonGirth (f : F ↪ E) (μ : Fin (m+1)) {g : ℕ}
    (hg : LabelledGirthGT (D.atCut (T.parent μ)).contactWagonCarrier g) :
    LabelledGirthGT ((D.pullEdges f).atCut ((T.pullTrain f).parent μ)).contactWagonCarrier g :=
  labelledGirthGT_of_injective_shrinking _ _ Subtype.val Subtype.val_injective
    (D.pull_wagon_subset T f μ) g hg

theorem pull_parameter (f : F ↪ E) (μ ν : Fin (m+1)) (allowed : Set V)
    (hp : D.Parameter T μ ν allowed) :
    (D.pullEdges f).Parameter (T.pullTrain f) μ ν allowed := by
  intro e g x he hx hy hn
  exact (T.pullTrain_rel f μ e g).mpr
    (hp (f e) (f g) x ((T.pullTrain_rel f ν e g).mp he) hx hy hn)

theorem pull_parameters (f : F ↪ E) (allowed : Fin m → Set V)
    (hp : D.Parameters T allowed) :
    (D.pullEdges f).Parameters (T.pullTrain f) allowed :=
  fun j => D.pull_parameter T f j.castSucc j.succ (allowed j) (hp j)

end ContactHypergraphData
end StructuralRamsey.Girth
