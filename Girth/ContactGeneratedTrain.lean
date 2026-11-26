import Girth.ContactTrainData

/-! The actual output hierarchy. The kernel of the tagged wagon
parent map is exactly the least equivalence containing the source
equivalences. This is proved by explicit shared-edge witnesses;
nesting, bottom equality and universal top then follow. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ : Type v}

namespace ContactTrainStrip
variable {m : ℕ}
    {D : ContactHypergraphData V E I} {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E m} {S : ContactTrainData E₀ m}
    (A : ContactTrainStrip D L T S)

abbrev Wagon (μ : Fin (m+1)) := ContactGlued (A.wagonGlue μ)

noncomputable def parentAt (μ : Fin (m+1)) : A.Edge → A.Wagon μ :=
  (A.atCut μ).output.parent

noncomputable def coreW (μ : Fin (m+1)) : T.Wagon μ ↪ A.Wagon μ :=
  contactCoreEmb (A.wagonGlue μ)

noncomputable def stdW (μ : Fin (m+1)) (i : I) : S.Wagon μ ↪ A.Wagon μ :=
  contactStandardEmb (A.wagonGlue μ) (A.wagonGlue_inj μ) i

theorem parentAt_core (μ : Fin (m+1)) (e : E) :
    A.parentAt μ (A.coreE e) = A.coreW μ (T.parent μ e) :=
  (A.atCut μ).output_parent_core e

theorem parentAt_std (μ : Fin (m+1)) (i : I) (f : E₀) :
    A.parentAt μ (A.stdE i f) = A.stdW μ i (S.parent μ f) :=
  (A.atCut μ).output_parent_standard i f

theorem parentAt_surj (μ : Fin (m+1)) : Function.Surjective (A.parentAt μ) :=
  (A.atCut μ).output_parent_surj

theorem shared_edge_eq (i : I) (f : E₀) (e : E)
    (h : A.edgeGlue i f = some e) : A.stdE i f = A.coreE e :=
  (contactStandardEmb_eq_core A.edgeGlue A.edge_inj i f e).mpr h

/-- Equality of a standard wagon and a core wagon is exactly
witnessed by an edge in their actual common strip. -/
theorem shared_parent_witness (μ : Fin (m+1)) (i : I) (f : E₀) (e : E)
    (h : A.parentAt μ (A.stdE i f) = A.parentAt μ (A.coreE e)) :
    ∃ f' e', A.edgeGlue i f' = some e' ∧
      S.parent μ f' = S.parent μ f ∧ T.parent μ e' = T.parent μ e := by
  rw [A.parentAt_std,A.parentAt_core] at h
  have hg := (contactStandardEmb_eq_core (A.wagonGlue μ) (A.wagonGlue_inj μ)
    i (S.parent μ f) (T.parent μ e)).mp h
  exact (A.wagonGlue_iff μ i _ _).mp hg

/-- Every equivalence relation containing the generators contains
the kernel of the actual tagged parent map. This is the least
equivalence property, not merely preservation of source classes. -/
theorem parentAt_kernel_minimal (μ : Fin (m+1))
    (rel : A.Edge → A.Edge → Prop) (hrel : Equivalence rel)
    (hc : ∀ e e', T.parent μ e = T.parent μ e' → rel (A.coreE e) (A.coreE e'))
    (hs : ∀ i f f', S.parent μ f = S.parent μ f' → rel (A.stdE i f) (A.stdE i f'))
    {u w : A.Edge} (h : A.parentAt μ u = A.parentAt μ w) : rel u w := by
  classical
  have cross (i : I) (f : E₀) (e : E)
      (he : A.parentAt μ (A.stdE i f) = A.parentAt μ (A.coreE e)) :
      rel (A.stdE i f) (A.coreE e) := by
    obtain ⟨f',e',hg,hf,he'⟩ := A.shared_parent_witness μ i f e he
    have h₁ := hs i f f' hf.symm
    rw [A.shared_edge_eq i f' e' hg] at h₁
    exact hrel.trans h₁ (hc e' e he')
  rcases contactGlued_cover A.edgeGlue A.edge_inj u with ⟨e,rfl⟩ | ⟨i,f,rfl⟩
  · rcases contactGlued_cover A.edgeGlue A.edge_inj w with ⟨e',rfl⟩ | ⟨j,f',rfl⟩
    · rw [A.parentAt_core,A.parentAt_core] at h
      exact hc e e' ((A.coreW μ).injective h)
    · exact hrel.symm (cross j f' e h.symm)
  · rcases contactGlued_cover A.edgeGlue A.edge_inj w with ⟨e,rfl⟩ | ⟨j,f',rfl⟩
    · exact cross i f e h
    · by_cases hij : i = j
      · subst j
        rw [A.parentAt_std,A.parentAt_std] at h
        exact hs i f f' ((A.stdW μ i).injective h)
      · have he : A.stdW μ i (S.parent μ f) = A.stdW μ j (S.parent μ f') := by
          rw [← A.parentAt_std,← A.parentAt_std]
          exact h
        have hcore : A.stdW μ i (S.parent μ f) ∈ Set.range (A.coreW μ) :=
          contactGlued_shared (A.wagonGlue μ) (A.wagonGlue_inj μ) i j hij _
            ⟨_,rfl⟩ ⟨_,he.symm⟩
        obtain ⟨r,hr⟩ := hcore
        obtain ⟨e,he'⟩ := T.surj μ r
        have hmid : A.parentAt μ (A.stdE i f) = A.parentAt μ (A.coreE e) := by
          rw [A.parentAt_std,A.parentAt_core,he',hr]
        exact hrel.trans (cross i f e hmid)
          (hrel.symm (cross j f' e (h.symm.trans hmid)))

/-- The actual generated nested output train. The proof of nesting
uses least equivalence, and bottom equality is a consequence of
source bottom equality, not an extra premise. -/
noncomputable def outputTrain : ContactTrainData A.Edge m where
  Wagon := A.Wagon
  parent := A.parentAt
  surj := A.parentAt_surj
  nested := by
    intro μ ν hμν u w h
    apply A.parentAt_kernel_minimal μ (fun u w => A.parentAt ν u = A.parentAt ν w)
      ⟨fun _ => rfl,fun h => h.symm,fun h h' => h.trans h'⟩
    · intro e e' he
      rw [A.parentAt_core,A.parentAt_core,T.nested μ ν hμν e e' he]
    · intro i f f' hf
      rw [A.parentAt_std,A.parentAt_std,S.nested μ ν hμν f f' hf]
    · exact h
  bottom := by
    intro u w h
    apply A.parentAt_kernel_minimal ⟨0,by omega⟩ (fun u w => u = w)
      ⟨fun _ => rfl,fun h => h.symm,fun h h' => h.trans h'⟩
    · intro e e' he
      exact congrArg A.coreE (T.bottom he)
    · intro i f f' hf
      exact congrArg (A.stdE i) (S.bottom hf)
    · exact h
  top := by
    let μ : Fin (m+1) := ⟨m,by omega⟩
    have hcore : ∀ e e', A.parentAt μ (A.coreE e) = A.parentAt μ (A.coreE e') := by
      intro e e'
      rw [A.parentAt_core,A.parentAt_core,T.top e e']
    have hstd : ∀ i f f', A.parentAt μ (A.stdE i f) = A.parentAt μ (A.stdE i f') := by
      intro i f f'
      rw [A.parentAt_std,A.parentAt_std,S.top f f']
    have hcon : ∀ u : A.Edge, ∃ e : E, A.parentAt μ u = A.parentAt μ (A.coreE e) := by
      intro u
      rcases contactGlued_cover A.edgeGlue A.edge_inj u with ⟨e,rfl⟩ | ⟨i,f,rfl⟩
      · exact ⟨e,rfl⟩
      · obtain ⟨f',e,h⟩ := A.shared_nonempty i
        refine ⟨e,?_⟩
        rw [← A.shared_edge_eq i f' e h]
        exact hstd i f f'
    intro u w
    obtain ⟨e,he⟩ := hcon u
    obtain ⟨e',he'⟩ := hcon w
    exact he.trans ((hcore e e').trans he'.symm)

/-- Exact restriction of the generated hierarchy to each standard
and to the core, at every cut. -/
theorem outputTrain_core_rel (μ : Fin (m+1)) (e e' : E) :
    A.outputTrain.toLevels.rel μ (A.coreE e) (A.coreE e') ↔ T.toLevels.rel μ e e' := by
  change A.parentAt μ (A.coreE e) = A.parentAt μ (A.coreE e') ↔ _
  rw [A.parentAt_core,A.parentAt_core]
  exact ⟨(A.coreW μ).injective,congrArg (A.coreW μ)⟩

theorem outputTrain_std_rel (μ : Fin (m+1)) (i : I) (f f' : E₀) :
    A.outputTrain.toLevels.rel μ (A.stdE i f) (A.stdE i f') ↔ S.toLevels.rel μ f f' := by
  change A.parentAt μ (A.stdE i f) = A.parentAt μ (A.stdE i f') ↔ _
  rw [A.parentAt_std,A.parentAt_std]
  exact ⟨(A.stdW μ i).injective,congrArg (A.stdW μ i)⟩

end ContactTrainStrip
end StructuralRamsey.Girth
