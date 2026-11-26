import Girth.ContactTrainPicture
import Girth.ContactMixedForestConverse

/-! Finite picture iteration for the actual train witness.
This isolates the forest-boost induction from the choice of
its recursive core witnesses. The input supply is explicitly
the smaller mixed-forest bound; all output invariants follow
from the constructed gluing, not from the supply. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B J : Type v} {m : ℕ}
variable {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
variable {base : B → Set X} [LinearOrder V] [LinearOrder X]

namespace ContactSeed
variable (A : ContactSeed D base J) (hm : 0 < m)
    (allowed : Fin m → Set X) (q : Fin (m+1) → ℕ)

/-- Initialize the common recursive state on literal disjoint
target copies. Orders are obtained by projection plus an
injective tie-breaker. -/
noncomputable def initialPicture [Finite V] [Finite E] [Finite J]
    (horder : ∀ j, StrictMono (A.vertex j))
    (hcovered : ∀ x, ∃ e, x ∈ D.edgeCarrier e)
    (hlin : ∀ μ, μ.val < m → (D.atCut (T.parent μ)).ContactLinear)
    (hg : D.WagonBounds T q)
    (hpar : ∀ i : J, D.Parameters T (fun j => A.vertex i ⁻¹' allowed j)) :
    ContactTrainPicture D T base allowed q := by
  classical
  let P := A.initialProjection
  letI : Fintype (J × V) := Fintype.ofFinite _
  let idx := Fintype.equivFin (J × V)
  let key (x : J × V) : X ×ₗ Fin (Fintype.card (J × V)) :=
    toLex (P.vertex x,idx x)
  let o : LinearOrder (J × V) := LinearOrder.lift' key
    (fun _ _ he => idx.injective (congrArg (fun z : X ×ₗ Fin (Fintype.card (J × V)) =>
      (ofLex z).2) he))
  have hb := T.disjoint_systemBounds D J hm q hlin hg
  refine {
    Vertex := J × V
    Edge := J × E
    Copy := J
    finiteV := inferInstance
    finiteE := inferInstance
    finiteC := inferInstance
    graph := D.disjointCopies J
    train := T.disjointTrain J hm
    projection := P
    family := A.initialFamily T hm
    order := o
    projection_order := ?_
    copy_order := ?_
    linear := (hb 0 (by exact hm)).linear.1
    covered := ?_
    parameters := ?_
    positive := fun μ _ h => hb μ h }
  · intro x y h
    change key x < key y at h
    exact (Prod.Lex.toLex_lt_toLex'.mp h).1
  · intro i x y h
    change key (i,x) < key (i,y)
    exact Prod.Lex.left _ _ (horder i h)
  · rintro ⟨i,x⟩
    obtain ⟨e,he⟩ := hcovered x
    exact ⟨(i,e),rfl,he⟩
  · intro j e f x he hx hy hn
    rcases e with ⟨i,e⟩
    rcases f with ⟨k,f⟩
    rcases x with ⟨l,x⟩
    have hx' : l = i ∧ x ∈ D.edgeCarrier e := hx
    have hy' : l = k ∧ x ∈ D.edgeCarrier f := hy
    obtain ⟨h₁,hx⟩ := hx'
    obtain ⟨h₂,hy⟩ := hy'
    subst l
    subst k
    have hco : T.parent j.succ e = T.parent j.succ f := by
      have hh := Quotient.exact he
      change j.succ.val = m ∨ i = i ∧ T.parent j.succ e = T.parent j.succ f at hh
      rcases hh with ht | ⟨_,ht⟩
      · have heq : j.succ = (⟨m,by omega⟩ : Fin (m+1)) := Fin.ext ht
        rw [heq]
        exact T.top _ _
      · exact ht
    have hfine := hpar i j e f x hco hx hy hn
    exact Quotient.sound (Or.inr ⟨rfl,hfine⟩)

theorem initialPicture_fullBounds [Finite V] [Finite E] [Finite J]
    (horder : ∀ j, StrictMono (A.vertex j))
    (hcovered : ∀ x, ∃ e, x ∈ D.edgeCarrier e)
    (hlin : ∀ μ, μ.val < m → (D.atCut (T.parent μ)).ContactLinear)
    (hg : D.WagonBounds T q)
    (hpar : ∀ i : J, D.Parameters T (fun j => A.vertex i ⁻¹' allowed j)) :
    (A.initialPicture hm allowed q horder hcovered hlin hg hpar).FullBounds :=
  T.disjoint_systemBounds D J hm q hlin hg

end ContactSeed

namespace ContactTrainPicture
variable {allowed : Fin m → Set X} {q : Fin (m+1) → ℕ}
    (P : ContactTrainPicture D T base allowed q)

/-- A full bottom system bound entails every smaller mixed
forest bound on the very same selected labels. -/
theorem forests_of_fullBounds (hm : 0 < m) {j : ℕ}
    (h : P.FullBounds) (hj : j ≤ q ⟨0,by omega⟩) :
    P.Forests j := by
  letI : Finite P.Vertex := P.finiteV
  letI : Fintype P.Vertex := Fintype.ofFinite _
  have hb := (P.train.bottom_systemGirth_iff P.graph _).mp (h ⟨0,by omega⟩ hm)
  have hf := P.graph.bottomCut.zero_mixedForests_of_systemGirth (fun _ => rfl) hb
  exact P.graph.bottomCut.zeroSmallMixedForests_mono
    (show P.Forests (q ⟨0,by omega⟩) from ⟨fun _ => hf.1,hf.2⟩) hj

/-- A supply of recursive core witnesses at the smaller forest
bound. The supply is requested only on actual nonempty strips,
and its conclusion contains no property of the output picture. -/
def BoostCoreSupply (j : ℕ) (Color : Type v) : Prop :=
  ∀ (Q : ContactTrainPicture D T base allowed q), Q.Forests j →
    ∀ b : B, Nonempty (Q.projection.StripEdge b) →
      ∃ C : Q.Core b, C.graph.bottomCut.ZeroSmallMixedForestsThrough (j-1) ∧
        LabelledGirthGT C.graph.edgeCarrier j ∧ C.family.Arrow Color

theorem exists_boost_chain {Color : Type v} [Nonempty Color] {j : ℕ}
    (hj : 2 ≤ j)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < m → 2 ≤ q μ)
    (supply : BoostCoreSupply (D := D) (T := T) (base := base)
      (allowed := allowed) (q := q) j Color)
    (hP : P.Forests j) (l : List B) :
    ∃ Q : ContactTrainPicture D T base allowed q, Q.Forests j ∧
      ContactFocusPicture.Chain Color P.focus Q.focus l := by
  classical
  induction l with
  | nil => exact ⟨P,hP,ContactFocusPicture.Chain.nil _⟩
  | cons b l ih =>
    obtain ⟨Q,hQ,hchain⟩ := ih
    by_cases hne : Nonempty (Q.projection.StripEdge b)
    · obtain ⟨C,hC,hg,hArrow⟩ := supply Q hQ b hne
      exact ⟨C.next hne hbase hq,C.next_forests hne hbase hq hj hQ hC hg,
        ContactFocusPicture.Chain.snoc hchain (C.next_focus hne hbase hq hArrow)⟩
    · have hstep : ContactFocusPicture.Step Q.focus Q.focus b Color := by
        intro χ
        refine ⟨Function.Embedding.refl _,id,fun _ => rfl,fun _ _ => rfl,
          Classical.choice (inferInstance : Nonempty Color),?_⟩
        intro e he
        exact (hne ⟨⟨e,he⟩⟩).elim
      exact ⟨Q,hQ,ContactFocusPicture.Chain.snoc hchain hstep⟩

/-- The actual finite boost iteration yields the arrow together
with its parameters, positive system bounds, order and mixed
forests. This is the finite-iteration part of the forest-boost
lemma; deriving the supply from the previous forest bound is
the separate induction on the class of input trains. -/
theorem boost_of_coreSupply [Fintype B] {Color : Type v} [Nonempty Color] {j : ℕ}
    (hj : 2 ≤ j)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < m → 2 ≤ q μ)
    (supply : BoostCoreSupply (D := D) (T := T) (base := base)
      (allowed := allowed) (q := q) j Color)
    (hP : P.Forests j)
    (hArrow : ∀ ρ : B → Color, ∃ i : P.Copy, ∃ c : Color,
      ∀ e : E, ρ (P.projection.edge ((P.family.emb i).edge e)) = c) :
    ∃ Q : ContactTrainPicture D T base allowed q, Q.Forests j ∧ Q.family.Arrow Color := by
  classical
  let l := (Finset.univ : Finset B).toList
  obtain ⟨Q,hQ,hchain⟩ := P.exists_boost_chain hj hbase hq supply hP l
  refine ⟨Q,hQ,hchain.arrow_of_base ?_ hArrow⟩
  intro b
  simp [l]

end ContactTrainPicture
end StructuralRamsey.Girth
