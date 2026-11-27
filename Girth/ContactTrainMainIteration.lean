import Girth.ContactTrainIteration

/-! Candidate continuation of the contact-graph validation.
The main iteration is separated from the supply of its recursive cores.
`Inv Q done` is the additional state of the proof: refinements on all
unprocessed nonempty strips. The core supply must construct the core
and prove retention of that invariant for the *actual* glued picture.
No final arrow or final picture is assumed. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B : Type v} {m : ℕ}
variable {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
variable {base : B → Set X} [LinearOrder V] [LinearOrder X]

namespace ContactTrainPicture
variable {allowed : Fin m → Set X} {q : Fin (m+1) → ℕ}

/-- The only nontrivial input of one main-induction step is an
actual recursive core, its mixed forests and arrow, and retention
of the extra invariant. All full system bounds of the output are
consequences of `Core.next_fullBounds`, not supply fields. -/
def MainCoreSupply
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (Inv : ContactTrainPicture D T base allowed q → List B → Prop)
    (Color : Type v) : Prop :=
  ∀ (Q : ContactTrainPicture D T base allowed q) (done : List B) (b : B),
    Q.FullBounds → Inv Q done → b ∉ done →
    ∀ hne : Nonempty (Q.projection.StripEdge b),
      ∃ C : Q.Core b,
        C.graph.bottomCut.ZeroSmallMixedForestsThrough (q 0) ∧
        (∀ e, (C.graph.edgeCarrier e).Nontrivial) ∧ C.family.Arrow Color ∧
        Inv (C.next hne hbase (fun μ _ h => hq μ h)) (b :: done)

/-- Process a list in reverse order, retaining the full train bounds
and the refinements still needed for all as yet unprocessed strips.
The order agrees with `ContactFocusPicture.Chain.snoc`. -/
theorem exists_main_chain (P : ContactTrainPicture D T base allowed q)
    {Color : Type v} [Nonempty Color]
    (hm : 0 < m)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (Inv : ContactTrainPicture D T base allowed q → List B → Prop)
    (hskip : ∀ Q done b, Inv Q done → Inv Q (b :: done))
    (supply : MainCoreSupply hbase hq Inv Color)
    (hP : P.FullBounds) (hInv : Inv P [])
    (l : List B) (hl : l.Nodup) :
    ∃ Q : ContactTrainPicture D T base allowed q,
      Q.FullBounds ∧ Inv Q l ∧ ContactFocusPicture.Chain Color P.focus Q.focus l := by
  classical
  induction l with
  | nil => exact ⟨P,hP,hInv,ContactFocusPicture.Chain.nil _⟩
  | cons b l ih =>
    obtain ⟨hb,hl'⟩ := List.nodup_cons.mp hl
    obtain ⟨Q,hQ,hI,hchain⟩ := ih hl'
    by_cases hne : Nonempty (Q.projection.StripEdge b)
    · obtain ⟨C,hC,hsize,hArrow,hI'⟩ := supply Q l b hQ hI hb hne
      exact ⟨C.next hne hbase (fun μ _ h => hq μ h),
        C.next_fullBounds hne hbase hq hm hQ hC hsize,
        hI',ContactFocusPicture.Chain.snoc hchain
          (C.next_focus hne hbase (fun μ _ h => hq μ h) hArrow)⟩
    · have hstep : ContactFocusPicture.Step Q.focus Q.focus b Color := by
        intro χ
        refine ⟨Function.Embedding.refl _,id,fun _ => rfl,fun _ _ => rfl,
          Classical.choice (inferInstance : Nonempty Color),?_⟩
        intro e he
        exact (hne ⟨⟨e,he⟩⟩).elim
      exact ⟨Q,hQ,hskip Q l b hI,ContactFocusPicture.Chain.snoc hchain hstep⟩

/-- The main finite picture iteration, with genuine output system
bounds and the arrow on the actual designated embeddings. Only the
local core supply is conditional. -/
theorem main_of_coreSupply (P : ContactTrainPicture D T base allowed q)
    [Fintype B] {Color : Type v} [Nonempty Color]
    (hm : 0 < m)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (Inv : ContactTrainPicture D T base allowed q → List B → Prop)
    (hskip : ∀ Q done b, Inv Q done → Inv Q (b :: done))
    (supply : MainCoreSupply hbase hq Inv Color)
    (hP : P.FullBounds) (hInv : Inv P [])
    (hArrow : ∀ ρ : B → Color, ∃ i : P.Copy, ∃ c : Color,
      ∀ e : E, ρ (P.projection.edge ((P.family.emb i).edge e)) = c) :
    ∃ Q : ContactTrainPicture D T base allowed q, Q.FullBounds ∧ Q.family.Arrow Color := by
  classical
  let l := (Finset.univ : Finset B).toList
  have hl : l.Nodup := Finset.nodup_toList _
  obtain ⟨Q,hQ,_,hchain⟩ := P.exists_main_chain hm hbase hq Inv hskip supply hP hInv l hl
  refine ⟨Q,hQ,hchain.arrow_of_base ?_ hArrow⟩
  intro b
  simp [l]

/-- With no additional refinement invariant (the cutoff-two case),
the core supply is precisely the forest-boosted local arrow.
The lemma remains conditional on its construction, not on the
conclusion of the train Ramsey theorem. -/
theorem main_without_refinement (P : ContactTrainPicture D T base allowed q)
    [Fintype B] {Color : Type v} [Nonempty Color]
    (hm : 0 < m)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (supply : ∀ (Q : ContactTrainPicture D T base allowed q), Q.FullBounds →
      ∀ b : B, Nonempty (Q.projection.StripEdge b) →
        ∃ C : Q.Core b,
          C.graph.bottomCut.ZeroSmallMixedForestsThrough (q 0) ∧
          (∀ e, (C.graph.edgeCarrier e).Nontrivial) ∧ C.family.Arrow Color)
    (hP : P.FullBounds)
    (hArrow : ∀ ρ : B → Color, ∃ i : P.Copy, ∃ c : Color,
      ∀ e : E, ρ (P.projection.edge ((P.family.emb i).edge e)) = c) :
    ∃ Q : ContactTrainPicture D T base allowed q, Q.FullBounds ∧ Q.family.Arrow Color := by
  apply P.main_of_coreSupply hm hbase hq (fun _ _ => True)
    (fun _ _ _ _ => True.intro) ?_ hP True.intro hArrow
  intro Q done b hQ _ _ hne
  obtain ⟨C,hC,hsize,hArrow⟩ := supply Q hQ b hne
  exact ⟨C,hC,hsize,hArrow,True.intro⟩

end ContactTrainPicture
end StructuralRamsey.Girth
