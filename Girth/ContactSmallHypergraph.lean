import Girth.ContactUniformTreeReduct
import Girth.ContactSmallRelational
import Girth.LinearityGirthTwo

/-! The small induced hypergraph consequence, including an edgeless target.
Tree amalgams are expressed in the single symmetric edge relation, so their
only gluing sets are whole edges and singletons supported by an edge on both
sides. No global vertex order is part of the conclusion. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe v
variable {U V W : Type v}

theorem contact_uniform_reduct_uniform {a : ℕ}
    (C : RelStructure (contactUniformLanguage a).withOrder W) :
    ∀ e ∈ contactUniformReduct a C, Nat.card e = a := by
  intro e he
  obtain ⟨x,hxi,_,hx⟩ := he
  let f (i : Fin a) : e := ⟨x i,hx ▸ (show x i ∈ Set.range x from ⟨i,rfl⟩)⟩
  have hfi : Function.Injective f := fun i j h => hxi (congrArg Subtype.val h)
  have hfs : Function.Surjective f := by
    intro z
    have hz : z.val ∈ Set.range x := hx.symm ▸ z.property
    obtain ⟨i,hi⟩ := hz
    exact ⟨i,Subtype.ext hi⟩
  let e' := Equiv.ofBijective f ⟨hfi,hfs⟩
  exact (Nat.card_congr e'.symm).trans (by simp)

/-- The relational arrow colours every edge of the unordered reduct.
The image is induced, and all of its edges receive the same colour. -/
theorem contact_uniform_arrow_transfer [Fintype U] [Finite V]
    [LinearOrder U] [LinearOrder V] {a : ℕ} (ha : Fintype.card U = a)
    (F : Set (Set V)) (hu : ∀ e ∈ F, Nat.card e = a)
    (C : RelStructure (contactUniformLanguage a).withOrder W)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding (contactUniformStructure a F).ordered C, S ⊆ copyCarrier b)
    (α : Embedding (contactUniformEdge a U).ordered (contactUniformStructure a F).ordered)
    (Color : Type v)
    (harr : StructuralRamsey.Arrow (contactUniformEdge a U).ordered
      (contactUniformStructure a F).ordered C Color) :
    ∀ χ : contactUniformReduct a C → Color, ∃ f : V ↪ W,
      (∀ e : Set V, e ∈ F ↔ f '' e ∈ contactUniformReduct a C) ∧
      ∃ c : Color, ∀ e : contactUniformReduct a C,
        e.val ⊆ Set.range f → χ e = c := by
  classical
  intro χ
  let A := contactUniformEdge a U
  have hH : supportCopies A.ordered C = contactUniformReduct a C :=
    contact_uniform_support_reduct ha F hu C hcover
  let ψ (a : Embedding A.ordered C) : Color := χ ⟨copyCarrier a,
    hH ▸ (show copyCarrier a ∈ supportCopies A.ordered C from ⟨a,rfl⟩)⟩
  obtain ⟨b,hb⟩ := harr ψ
  refine ⟨b.toFunctionEmbedding,contact_uniform_copy_induced F hu b,ψ (b.comp α),?_⟩
  intro e he
  have he' : e.val ∈ supportCopies A.ordered C := hH.symm ▸ e.property
  obtain ⟨eA,ha'⟩ := he'
  have hex (x : U) : ∃ y : V, eA x = b y := by
    obtain ⟨y,hy⟩ := he (ha'.symm ▸ (show eA x ∈ copyCarrier eA from ⟨x,rfl⟩))
    exact ⟨y,hy.symm⟩
  let d := eA.factorThroughRange b hex
  have hEq : b.comp d = eA := Embedding.ext (fun x => (Classical.choose_spec (hex x)).symm)
  have hmono := hb d α
  change ψ (b.comp d) = ψ (b.comp α) at hmono
  rw [hEq] at hmono
  have hχ : e = (⟨copyCarrier eA,hH ▸
      (show copyCarrier eA ∈ supportCopies A.ordered C from ⟨eA,rfl⟩)⟩ : contactUniformReduct a C) :=
    Subtype.ext ha'
  rw [hχ]
  exact hmono

/-- Literal unordered form of the small induced subhypergraph
corollary. The target tree is built from copies of the original
hypergraph by free amalgamation over edges and supported points. -/
def ContactUniformSmallRamseyWitness (a : ℕ) (F : Set (Set V))
    (s : ℕ) (Color : Type v) : Prop :=
  ∃ (W : Type v) (H : Set (Set W)), Finite W ∧
    (∀ e ∈ H, Nat.card e = a) ∧
    (∀ χ : H → Color, ∃ f : V ↪ W,
      (∀ e : Set V, e ∈ F ↔ f '' e ∈ H) ∧
      ∃ c : Color, ∀ e : H, e.val ⊆ Set.range f → χ e = c) ∧
    ∀ Z : Set W, Nat.card Z ≤ s →
      ∃ (X : Type v) (T : RelStructure (contactUniformLanguage a) X)
        (e : Embedding ((contactUniformStructure a H).induce Z) T),
        ASupportedTreeAmalgam (contactUniformEdge a (ULift.{v} (Fin a)))
          (contactUniformStructure a F) X T

/-- The edgeless target requires no construction and no nonempty
edge assumption: every induced subhypergraph already embeds into F. -/
theorem contactUniformSmallRamsey_edgeless [Finite V]
    (a : ℕ) (F : Set (Set V)) (hF : F = ∅) (s : ℕ)
    (Color : Type v) [Nonempty Color] :
    ContactUniformSmallRamseyWitness a F s Color := by
  classical
  refine ⟨V,F,inferInstance,?_,?_,?_⟩
  · intro e he
    exact (hF ▸ he : e ∈ (∅ : Set (Set V))).elim
  · intro χ
    refine ⟨Function.Embedding.refl V,?_,Classical.choice (inferInstance : Nonempty Color),?_⟩
    · intro e
      simp
    · intro e _
      exact (hF ▸ e.property : e.val ∈ (∅ : Set (Set V))).elim
  · intro Z _
    exact ⟨V,contactUniformStructure a F,RelStructure.inclusion _ Z,
      ASupportedTreeAmalgam.copy (Iso.refl _)⟩

/-- Every finite linear uniform hypergraph has an edge-Ramsey
witness whose induced subhypergraphs on at most s vertices embed
into supported tree amalgams of copies of the target. -/
theorem contactUniformSmallRamsey [Finite V]
    (a : ℕ) (ha₂ : 2 ≤ a) (F : Set (Set V))
    (hu : ∀ e ∈ F, Nat.card e = a) (hlin : LinearEdgeSet F)
    (s : ℕ) (Color : Type v) [Finite Color] [Nonempty Color] :
    ContactUniformSmallRamseyWitness a F s Color := by
  classical
  by_cases hne : F.Nonempty
  · letI : Fintype V := Fintype.ofFinite _
    let ev := Fintype.equivFin V
    letI : LinearOrder V := LinearOrder.lift' ev ev.injective
    let U := ULift.{v} (Fin a)
    letI : Fintype U := inferInstanceAs (Fintype (ULift.{v} (Fin a)))
    letI : LinearOrder U := LinearOrder.lift' (fun x : U => x.down)
      (fun x y h => ULift.ext h)
    have ha : Fintype.card U = a := by simp [U]
    let A := contactUniformEdge a U
    let B := contactUniformStructure a F
    have hSource : supportCopies A.ordered B.ordered = F :=
      contact_uniform_support_ordered ha F hu
    obtain ⟨e,he⟩ := hne
    have he' : e ∈ supportCopies A.ordered B.ordered := hSource.symm ▸ he
    obtain ⟨α,_⟩ := he'
    obtain ⟨W,C,o,hfin,hord,harr,hcover,hcomp,_⟩ :=
      contactRelationalGirthRamsey_carriers A B (ha.symm ▸ ha₂) α 2 (max 2 s)
        (by omega) (Nat.le_max_left _ _)
        (hSource.symm ▸ girthGT_two_of_linearEdgeSet hlin) Color
    letI : Finite W := hfin
    refine ⟨W,contactUniformReduct a C,hfin,contact_uniform_reduct_uniform C,
      contact_uniform_arrow_transfer ha F hu C hcover α Color harr,?_⟩
    intro Z hZ
    obtain ⟨X,T,e,hT⟩ := contact_small_induced_supported 2 (max 2 s) hcover hcomp Z
      (hZ.trans (Nat.le_max_right _ _))
    exact ⟨X,T.orderReduct,(contactOrderReduct_embedding e).comp
      (contact_uniform_induced_reduct ha F hu C hcover Z),hT.contact_orderReduct⟩
  · exact contactUniformSmallRamsey_edgeless a F (Set.not_nonempty_iff_eq_empty.mp hne) s Color

end StructuralRamsey.Girth
