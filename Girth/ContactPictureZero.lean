import Girth.ContactDisjointCopies
import Girth.ContactTrainBottom

/-! The whole initial train, obtained by taking vertex-disjoint
copies at every proper cut and identifying only the universal top.
The quotient labels at the proper cuts are bijective to pairs
(component, original wagon). -/

namespace StructuralRamsey.Girth
universe v
variable {V E I J : Type v}

namespace ContactTrainData
variable {m : ℕ} (T : ContactTrainData E m)

def disjointLevels (J : Type v) (hm : 0 < m) : EdgeTrainLevels (J × E) m where
  rel := fun μ e f => μ.val = m ∨ e.1 = f.1 ∧ T.parent μ e.2 = T.parent μ f.2
  equivalent := by
    intro μ
    refine ⟨fun e => Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · intro e f h
      rcases h with h | ⟨h₁,h₂⟩
      · exact Or.inl h
      · exact Or.inr ⟨h₁.symm,h₂.symm⟩
    · intro e f g h h'
      rcases h with h | ⟨h₁,h₂⟩
      · exact Or.inl h
      · rcases h' with h' | ⟨h₃,h₄⟩
        · exact Or.inl h'
        · exact Or.inr ⟨h₁.trans h₃,h₂.trans h₄⟩
  nested := by
    intro μ ν hle e f h
    rcases h with ht | ⟨h₁,h₂⟩
    · left
      have hn := ν.isLt
      change μ.val ≤ ν.val at hle
      omega
    · exact Or.inr ⟨h₁,T.nested μ ν hle _ _ h₂⟩
  bottom := by
    intro e f
    constructor
    · rintro (h | ⟨h₁,h₂⟩)
      · change 0 = m at h
        omega
      · exact Prod.ext h₁ (T.bottom h₂)
    · rintro rfl
      exact Or.inr ⟨rfl,rfl⟩
  top := fun _ _ => Or.inl rfl

def disjointTrain (J : Type v) (hm : 0 < m) : ContactTrainData (J × E) m :=
  (T.disjointLevels J hm).toContactTrain

/-- Proper wagon labels in the actual disjoint train are exactly
the component-labelled original wagons. -/
noncomputable def disjointWagonEquiv (J : Type v) (hm : 0 < m)
    (μ : Fin (m+1)) (hproper : μ.val < m) :
    (T.disjointTrain J hm).Wagon μ ≃ J × T.Wagon μ := by
  let g : (J × E) → J × T.Wagon μ := fun e => (e.1,T.parent μ e.2)
  have hiff (e f : J × E) :
      (T.disjointLevels J hm).rel μ e f ↔ g e = g f := by
    constructor
    · rintro (h | ⟨h₁,h₂⟩)
      · omega
      · exact Prod.ext h₁ h₂
    · intro h
      exact Or.inr ⟨congrArg (fun z : J × T.Wagon μ => z.1) h,
        congrArg (fun z : J × T.Wagon μ => z.2) h⟩
  let f : (T.disjointTrain J hm).Wagon μ → J × T.Wagon μ :=
    Quotient.lift g (fun _ _ h => (hiff _ _).mp h)
  have hinj : Function.Injective f := by
    intro a b h
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b => exact Quotient.sound ((hiff a b).mpr h)
  have hsurj : Function.Surjective f := by
    rintro ⟨j,p⟩
    obtain ⟨e,he⟩ := T.surj μ p
    exact ⟨(T.disjointTrain J hm).parent μ (j,e),Prod.ext rfl he⟩
  exact Equiv.ofBijective f ⟨hinj,hsurj⟩

theorem disjointWagonEquiv_parent (J : Type v) (hm : 0 < m)
    (μ : Fin (m+1)) (hproper : μ.val < m) (e : J × E) :
    T.disjointWagonEquiv J hm μ hproper ((T.disjointTrain J hm).parent μ e) =
      (e.1,T.parent μ e.2) := rfl

/-- Picture zero carries the complete vector of proper-cut
system-girth bounds of the initial train. No copy-system axiom is
assumed of the original train. -/
theorem disjoint_systemBounds (D : ContactHypergraphData V E I)
    (J : Type v) (hm : 0 < m) (q : Fin (m+1) → ℕ)
    (hlin : ∀ μ, μ.val < m → (D.atCut (T.parent μ)).ContactLinear)
    (hg : ∀ μ, μ.val < m →
      LabelledGirthGT (D.atCut (T.parent μ)).contactWagonCarrier (q μ)) :
    (D.disjointCopies J).SystemBounds (T.disjointTrain J hm) q := by
  intro μ hproper
  let e := T.disjointWagonEquiv J hm μ hproper
  let A := (D.disjointCopies J).atCut ((T.disjointTrain J hm).parent μ)
  have he : A.relabelWagons e = D.disjointCut J (T.parent μ) := by
    unfold A ContactHypergraphData.disjointCut
    rw [ContactHypergraphData.relabel_atCut]
    have hp : e ∘ (T.disjointTrain J hm).parent μ =
        (fun f : J × E => (f.1,T.parent μ f.2)) := by
      funext f
      exact T.disjointWagonEquiv_parent J hm μ hproper f
    rw [hp]
  have h := D.disjoint_systemGirth (T.parent μ) (T.surj μ)
    (J := J) (hlin μ hproper) (hg μ hproper)
  exact (A.relabel_systemGirth_iff e).mp (he.symm ▸ h)

/-- Initial parameter sets pull back from the original parts. The
real vertex already determines its component, so the top relation
does not introduce a spurious common vertex between components. -/
theorem disjoint_parameters (D : ContactHypergraphData V E I)
    (J : Type v) (hm : 0 < m) (allowed : Fin m → Set V)
    (h : D.Parameters T allowed) :
    (D.disjointCopies J).Parameters (T.disjointTrain J hm)
      (fun k => Prod.snd ⁻¹' allowed k) := by
  intro k e f x hpar hxe hxf hnot
  have hfirst : e.1 = f.1 := hxe.1.symm.trans hxf.1
  have heq : T.parent k.succ e.2 = T.parent k.succ f.2 := by
    have hp := Quotient.exact hpar
    change k.succ.val = m ∨ e.1 = f.1 ∧ T.parent k.succ e.2 = T.parent k.succ f.2 at hp
    rcases hp with htop | ⟨_,hp⟩
    · have he : k.succ = (⟨m,by omega⟩ : Fin (m+1)) := Fin.ext htop
      rw [he]
      exact T.top _ _
    · exact hp
  have hfine := h k e.2 f.2 x.2 heq hxe.2 hxf.2 hnot
  apply Quotient.sound
  exact Or.inr ⟨hfirst,hfine⟩

end ContactTrainData
end StructuralRamsey.Girth
