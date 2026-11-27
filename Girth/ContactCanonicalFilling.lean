import Girth.ContactTrainData
import Girth.ContactSubstitution

/-! Canonical edge filling for the shorter-train construction.
Every edge of the new hypergraph is a genuine occurrence
(old edge, template edge). The first partition groups occurrences
by their old edge, and every higher cut inherits the original
wagon labels. This avoids constructing quotient equivalences
after the filling has been formed. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X F J : Type v}

/-- A fixed template placed bijectively onto every old edge,
including coverage by the template's edges. -/
structure ContactFilling (D : ContactHypergraphData V E I)
    (L : ContactHypergraphData X F J) where
  place : E → X ↪ V
  range_eq : ∀ e, Set.range (place e) = D.edgeCarrier e
  template_cover : ∀ x, ∃ f, x ∈ L.edgeCarrier f
  template_nonempty : Nonempty F

namespace ContactFilling
variable {D : ContactHypergraphData V E I} {L : ContactHypergraphData X F J}
    (A : ContactFilling D L)

def output : ContactHypergraphData V (E × F) I where
  edgeCarrier := fun p => A.place p.1 '' L.edgeCarrier p.2
  copyCarrier := D.copyCarrier
  copyEdges := fun i => Prod.fst ⁻¹' D.copyEdges i

theorem output_contained (p : E × F) :
    A.output.edgeCarrier p ⊆ D.edgeCarrier p.1 := by
  rintro x ⟨y,_,rfl⟩
  rw [← A.range_eq]
  exact ⟨y,rfl⟩

theorem output_cover (e : E) (x : V) (hx : x ∈ D.edgeCarrier e) :
    ∃ f : F, x ∈ A.output.edgeCarrier (e,f) := by
  rw [← A.range_eq] at hx
  obtain ⟨y,rfl⟩ := hx
  obtain ⟨f,hf⟩ := A.template_cover y
  exact ⟨f,y,hf,rfl⟩

theorem output_linear
    (hD : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hL : ∀ e f : F, e ≠ f → (L.edgeCarrier e ∩ L.edgeCarrier f).Subsingleton) :
    ∀ e f : E × F, e ≠ f → (A.output.edgeCarrier e ∩ A.output.edgeCarrier f).Subsingleton := by
  intro e f hne x hx y hy
  by_cases h : e.1 = f.1
  · rcases e with ⟨e,a⟩
    rcases f with ⟨f,b⟩
    change e = f at h
    subst f
    have hab : a ≠ b := fun he => hne (congrArg (Prod.mk e) he)
    obtain ⟨u,hu,he⟩ := hx.1
    obtain ⟨w,hw,hf⟩ := hx.2
    have heq := (A.place e).injective (he.trans hf.symm)
    subst w
    obtain ⟨u',hu',he'⟩ := hy.1
    obtain ⟨w',hw',hf'⟩ := hy.2
    have heq' := (A.place e).injective (he'.trans hf'.symm)
    subst w'
    exact he.symm.trans ((congrArg (A.place e) (hL a b hab ⟨hu,hw⟩ ⟨hu',hw'⟩)).trans he')
  · exact hD e.1 f.1 h
      ⟨A.output_contained e hx.1,A.output_contained f hx.2⟩
      ⟨A.output_contained e hy.1,A.output_contained f hy.2⟩

variable {m : ℕ} (T : ContactTrainData E m)

def fillWagon (_A : ContactFilling D L) : Fin (m+2) → Type v :=
  Fin.cases (E × F) T.Wagon

def fillParent : (μ : Fin (m+2)) → E × F → A.fillWagon T μ :=
  Fin.cases id (fun ν p => T.parent ν p.1)

theorem fillParent_zero (p : E × F) :
    A.fillParent T 0 p = p := rfl

theorem fillParent_succ (μ : Fin (m+1)) (p : E × F) :
    A.fillParent T μ.succ p = T.parent μ p.1 := rfl

/-- The first actual cut is the old edge partition, and each
higher cut is an old parent map applied to the old edge label. -/
noncomputable def fillTrain : ContactTrainData (E × F) (m+1) where
  Wagon := A.fillWagon T
  parent := A.fillParent T
  surj := by
    intro μ
    refine Fin.cases ?_ (fun ν => ?_) μ
    · exact Function.surjective_id
    · intro p
      obtain ⟨e,he⟩ := T.surj ν p
      let f : F := Classical.choice A.template_nonempty
      exact ⟨(e,f),he⟩
  nested := by
    intro μ ν
    refine Fin.cases ?_ (fun i => ?_) μ
    · intro _ e f he
      have h : e = f := he
      subst f
      rfl
    · refine Fin.cases ?_ (fun j => ?_) ν
      · intro h
        have hf : i.val+1 ≤ 0 := h
        omega
      · intro h e f he
        have hij : i ≤ j := by
          change i.val+1 ≤ j.val+1 at h
          exact Nat.le_of_succ_le_succ h
        exact T.nested i j hij e.1 f.1 he
  bottom := Function.injective_id
  top := by
    intro e f
    exact T.top e.1 f.1

/-- The inherited system at any positive cut is an actual
ContactSubstitution of the old system, so all its wagon carriers,
cliques and girth bounds survive by the certified theorem. -/
def atInheritedCut (μ : Fin (m+1))
    (hNonempty : ∀ e, (D.edgeCarrier e).Nonempty)
    (hD : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hL : ∀ e f : F, e ≠ f → (L.edgeCarrier e ∩ L.edgeCarrier f).Subsingleton) :
    ContactSubstitution (D.atCut (T.parent μ))
      (A.output.atCut ((A.fillTrain T).parent μ.succ)) where
  cover := Prod.fst
  contained := A.output_contained
  covering := by
    intro e x hx
    obtain ⟨f,hf⟩ := A.output_cover e x hx
    exact ⟨(e,f),rfl,hf⟩
  old_nonempty := hNonempty
  parent_eq := fun _ => rfl
  copyCarrier_eq := fun _ => rfl
  copyEdges_iff := fun _ _ => Iff.rfl
  newEdgeLinear := A.output_linear hD hL

theorem preserves_inherited_systemGirth (μ : Fin (m+1)) {q : ℕ}
    (hNonempty : ∀ e, (D.edgeCarrier e).Nonempty)
    (hL : ∀ e f : F, e ≠ f → (L.edgeCarrier e ∩ L.edgeCarrier f).Subsingleton)
    (hD : (D.atCut (T.parent μ)).ContactSystemGirthGT q) :
    (A.output.atCut ((A.fillTrain T).parent μ.succ)).ContactSystemGirthGT q :=
  (A.atInheritedCut T μ hNonempty hD.linear.1 hL).preserves_systemGirth hD

/-- The positive proper cuts of the filled train are precisely
the proper cuts of the old train (including its bottom). -/
theorem preserves_positiveBounds (q : Fin (m+1) → ℕ)
    (hNonempty : ∀ e, (D.edgeCarrier e).Nonempty)
    (hL : ∀ e f : F, e ≠ f → (L.edgeCarrier e ∩ L.edgeCarrier f).Subsingleton)
    (hD : D.SystemBounds T q) :
    A.output.PositiveBounds (A.fillTrain T)
      (Fin.cases 0 q) := by
  intro μ
  refine Fin.cases ?_ (fun ν => ?_) μ
  · intro h
    change 0 < 0 at h
    omega
  · intro _ h
    have hp : ν.val < m := by change ν.val+1 < m+1 at h; omega
    exact A.preserves_inherited_systemGirth T ν hNonempty hL (hD ν hp)

/-- The new first parameter is guaranteed by the allowed
intersections of distinct template edges in each placement. -/
theorem first_parameter (allowed : Set V)
    (hL : ∀ e (a b : F), a ≠ b →
      A.place e '' (L.edgeCarrier a ∩ L.edgeCarrier b) ⊆ allowed) :
    A.output.Parameter (A.fillTrain T) 0 (Fin.succ (0 : Fin (m+1))) allowed := by
  rintro ⟨e,a⟩ ⟨f,b⟩ x hpar hx hy hnot
  have he : e = f := T.bottom hpar
  subst f
  by_contra hne
  have hab : a ≠ b := fun he => hne (congrArg (Prod.mk e) he)
  obtain ⟨u,hu,he⟩ := hx
  obtain ⟨v,hv,hf⟩ := hy
  have heq := (A.place e).injective (he.trans hf.symm)
  subst v
  exact hnot (hL e a b hab ⟨u,⟨hu,hv⟩,he⟩)

theorem inherited_parameter (μ ν : Fin (m+1)) (allowed : Set V)
    (h : D.Parameter T μ ν allowed) :
    A.output.Parameter (A.fillTrain T) μ.succ ν.succ allowed :=
  fun e f x he hx hy hn => h e.1 f.1 x he
    (A.output_contained e hx) (A.output_contained f hy) hn

end ContactFilling
end StructuralRamsey.Girth
