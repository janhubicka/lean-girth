import Girth.ForestShortCycleProjection
import Girth.ForestMixedLocalForestBridge
import Girth.ForestOverlapTransfer
import Girth.ForestMultiEdgeSupport
import Mathlib.Order.Hom.Set
import Girth.FreeAttachmentOrderExtension
import Girth.LocalCoveredWitnessReduction

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v w
variable {V W P : Type v}

/-- Restrict the edges to the subtype of retained vertices. The restoration
theorem requires that every original edge lies in that subtype. -/
def inducedSupport (S : Set V) (H : Set (Set V)) : Set (Set S) :=
  (fun e => Subtype.val ⁻¹' e) '' H

namespace IsolatedRestoration

variable (S : Set V) (H : Set (Set V)) (K : Set (Set W))
variable (family : Set (StrongSupportEmbedding (inducedSupport S H) K))

abbrev Selection := {f : StrongSupportEmbedding (inducedSupport S H) K // f ∈ family}
abbrev Vertex := RelStructure.Attachment.Vertex S (W := W) (I := Selection S H K family)

/-- Include the existing witness as the vertices that precede restoration. -/
def core : W ↪ Vertex S H K family := ⟨Sum.inl, Sum.inl_injective⟩

def edges : Set (Set (Vertex S H K family)) :=
  (fun e : Set W => core S H K family '' e) '' K

private def emptyLanguage : RelLanguage.{0} := ⟨PEmpty, PEmpty.elim⟩
private def bare (X : Type v) : RelStructure emptyLanguage X :=
  ⟨fun p => PEmpty.elim p⟩

private def boundary (i : Selection S H K family) :
    Embedding ((bare V).induce S) (bare W) :=
  ⟨i.1.toFun, i.1.injective, fun p => PEmpty.elim p⟩

/-- Each restored isolated point is indexed by its own selected embedding. -/
noncomputable def lift (i : Selection S H K family) : V → Vertex S H K family :=
  RelStructure.Attachment.copyMap (bare V) S (bare W) (boundary S H K family) i

@[simp] theorem lift_mem (i : Selection S H K family) (x : V) (hx : x ∈ S) :
    lift S H K family i x = core S H K family (i.1 ⟨x, hx⟩) :=
  RelStructure.Attachment.copyMap_mem i x hx

@[simp] theorem lift_not_mem (i : Selection S H K family) (x : V) (hx : x ∉ S) :
    lift S H K family i x = .inr (i, ⟨x, hx⟩) :=
  RelStructure.Attachment.copyMap_not_mem i x hx

theorem lift_image (hSupport : ∀ e ∈ H, e ⊆ S)
    (i : Selection S H K family) {e : Set V} (he : e ∈ H) :
    lift S H K family i '' e =
      core S H K family '' (i.1 '' (Subtype.val ⁻¹' e : Set S)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨i.1 ⟨x, hSupport e he hx⟩, ⟨⟨x, hSupport e he hx⟩, hx, rfl⟩,
      (lift_mem S H K family i x (hSupport e he hx)).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x.1, hx, lift_mem S H K family i x.1 x.2⟩

/-- Old edges do not use the new vertices. In particular a selected lift is
strong whenever its restriction to the old vertices is strong. -/
noncomputable def strongLift (hSupport : ∀ e ∈ H, e ⊆ S)
    (i : Selection S H K family) : StrongSupportEmbedding H (edges S H K family) where
  toFun := lift S H K family i
  injective := RelStructure.Attachment.copyMap_injective i
  map_edge := by
    intro e he
    have hr : (Subtype.val ⁻¹' e : Set S) ∈ inducedSupport S H := ⟨e, he, rfl⟩
    obtain ⟨E, hE, hEq⟩ := i.1.map_edge _ hr
    exact ⟨core S H K family '' E, ⟨E, hE, rfl⟩,
      (congrArg (Set.image (core S H K family)) hEq).trans
        (lift_image S H K family hSupport i he).symm⟩
  reflect_edge := by
    rintro _ ⟨E, hE, rfl⟩ hMeet
    have hIn (y : W) (hy : core S H K family y ∈ Set.range (lift S H K family i)) :
        y ∈ Set.range i.1 := by
      obtain ⟨x, hx⟩ := hy
      have hs : x ∈ S := RelStructure.Attachment.mem_of_copyMap_eq_inl hx
      rw [lift_mem S H K family i x hs] at hx
      exact ⟨⟨x, hs⟩, (core S H K family).injective hx⟩
    have hOld : ¬ (E ∩ Set.range i.1).Subsingleton := by
      intro hSmall
      apply hMeet
      rintro _ ⟨⟨a, ha, rfl⟩, hfa⟩ _ ⟨⟨b, hb, rfl⟩, hfb⟩
      exact congrArg (core S H K family)
        (hSmall ⟨ha, hIn a hfa⟩ ⟨hb, hIn b hfb⟩)
    obtain ⟨_, ⟨e, he, rfl⟩, hEq⟩ := i.1.reflect_edge E hE hOld
    exact ⟨e, he, (congrArg (Set.image (core S H K family)) hEq).trans
      (lift_image S H K family hSupport i he).symm⟩

def part (sourcePart : V → P) (oldPart : W → P) :
    Vertex S H K family → P
  | .inl y => oldPart y
  | .inr (_, x) => sourcePart x.1

theorem strongLift_preserves_parts (hSupport : ∀ e ∈ H, e ⊆ S)
    (sourcePart : V → P) (oldPart : W → P)
    (hPart : ∀ (i : Selection S H K family) (x : S), oldPart (i.1 x) = sourcePart x.1)
    (i : Selection S H K family) (x : V) :
    part S H K family sourcePart oldPart (strongLift S H K family hSupport i x) =
      sourcePart x := by
  change part S H K family sourcePart oldPart (lift S H K family i x) = _
  by_cases hx : x ∈ S
  · rw [lift_mem S H K family i x hx]
    exact hPart i ⟨x, hx⟩
  · rw [lift_not_mem S H K family i x hx]
    rfl

/-- Transfer the common old order to the actual restoration, simultaneously
preserving the prescribed order of every entire selected copy. -/
theorem exists_order [LinearOrder V] [LinearOrder W] [Finite V]
    [LinearOrder (Selection S H K family)]
    (hMono : ∀ i : Selection S H K family, StrictMono i.1) :
    ∃ o : LinearOrder (Vertex S H K family),
      (∀ x y : W, x < y → @LT.lt _ o.toLT (core S H K family x) (core S H K family y)) ∧
      ∀ (i : Selection S H K family) (x y : V), x < y →
        @LT.lt _ o.toLT (lift S H K family i x) (lift S H K family i y) := by
  obtain ⟨o, hCore, hCopy⟩ := RelStructure.Attachment.exists_linearOrder_attachment
    (bare V) S (bare W) (boundary S H K family) hMono
  exact ⟨o, fun _ _ h => hCore h, fun i _ _ h => hCopy i h⟩

theorem edgeTransversal (sourcePart : V → P) (oldPart : W → P)
    (hTrans : EdgeTransversal K oldPart) :
    EdgeTransversal (edges S H K family) (part S H K family sourcePart oldPart) := by
  rintro _ ⟨e, he, rfl⟩ p
  obtain ⟨x, hx, hUnique⟩ := hTrans e he p
  refine ⟨core S H K family x, ⟨⟨x, hx.1, rfl⟩, hx.2⟩, ?_⟩
  rintro y ⟨⟨z, hz, rfl⟩, hp⟩
  exact congrArg (core S H K family) (hUnique z ⟨hz, hp⟩)

theorem girth_three [Nonempty W] (hGirth : GirthGT K 3) :
    GirthGT (edges S H K family) 3 := by
  classical
  let p : Vertex S H K family → W := Sum.elim id (fun _ => Classical.choice inferInstance)
  have hBack (e : Set W) : p '' (core S H K family '' e) = e := by
    rw [Set.image_image]
    exact Set.image_id _
  apply girthGT_three_of_edgeProjection p _ _ _ hGirth
  · rintro _ ⟨e, he, rfl⟩
    rw [hBack]
    exact he
  · rintro _ ⟨e, _, rfl⟩ _ ⟨e', _, rfl⟩ h
    exact congrArg (Set.image (core S H K family))
      ((hBack e).symm.trans (h.trans (hBack e')))
  · rintro _ ⟨e, _, rfl⟩ _ ⟨a, _, rfl⟩ _ ⟨b, _, rfl⟩ h
    exact congrArg (core S H K family) h

/-- The same selected label gives its monochromatic copy after restoration. -/
theorem covered_and_arrow (hSupport : ∀ e ∈ H, e ⊆ S)
    {κ : Type w} (hCovered : StrongSupportCoversEdges (inducedSupport S H) K family)
    (hArrow : StrongSupportEdgeArrow (inducedSupport S H) family κ) :
    let F := Set.range (strongLift S H K family hSupport)
    StrongSupportCoversEdges H (edges S H K family) F ∧
    StrongSupportEdgeArrow H F κ := by
  constructor
  · rintro _ ⟨E, he, rfl⟩
    obtain ⟨f, hf, _, ⟨e, he', rfl⟩, hEq⟩ := hCovered E he
    let i : Selection S H K family := ⟨f, hf⟩
    refine ⟨strongLift S H K family hSupport i, ⟨i, rfl⟩, e, he', ?_⟩
    change core S H K family '' E = lift S H K family i '' e
    rw [lift_image S H K family hSupport i he']
    exact congrArg (Set.image (core S H K family)) hEq
  · intro χ
    let χ₀ : K → κ :=
      fun E => χ ⟨core S H K family '' E.1, ⟨E.1, E.2, rfl⟩⟩
    obtain ⟨f, hf, c, hMono⟩ := hArrow χ₀
    let i : Selection S H K family := ⟨f, hf⟩
    refine ⟨strongLift S H K family hSupport i, ⟨i, rfl⟩, c, ?_⟩
    intro e he
    have hr : (Subtype.val ⁻¹' e : Set S) ∈ inducedSupport S H := ⟨e, he, rfl⟩
    have hEq :
        (⟨(strongLift S H K family hSupport i) '' e,
          (strongLift S H K family hSupport i).mappedEdge_mem e he⟩ :
          edges S H K family) =
        ⟨core S H K family '' (f '' (Subtype.val ⁻¹' e : Set S)),
          ⟨_, f.mappedEdge_mem _ hr, rfl⟩⟩ := Subtype.ext
        (lift_image S H K family hSupport i he)
    rw [hEq]
    exact hMono _ hr

/-- Adding isolated points to individual copies preserves every bounded
mixed forest. The tree and its pairwise separators are the original ones. -/
theorem mixedForest [LinearOrder V] [LinearOrder W] [Finite V]
    (hSupport : ∀ e ∈ H, e ⊆ S)
    (hMono : ∀ i : Selection S H K family, StrictMono i.1)
    (hTwo : ∃ e₀ ∈ inducedSupport S H, ∃ e₁ ∈ inducedSupport S H, e₀ ≠ e₁)
    (m : ℕ)
    (hMixed : FiniteMixedForestThrough
      (fun P => (∃ f ∈ family, P = f.supportPiece) ∨
        (∃ e ∈ K, P = HypergraphPiece.oneEdge e)) m) :
    FiniteMixedForestThrough
      (fun P => (∃ i : Selection S H K family,
          P = (strongLift S H K family hSupport i).supportPiece) ∨
        (∃ e ∈ edges S H K family, P = HypergraphPiece.oneEdge e)) m := by
  classical
  let I := Selection S H K family
  let old : I ⊕ K → HypergraphPiece W :=
    mixedOwnerSmall (fun i : I => i.1.supportPiece) Subtype.val
  let new : I ⊕ K → HypergraphPiece (Vertex S H K family) :=
    mixedOwnerSmall (fun i : I => (strongLift S H K family hSupport i).supportPiece)
      (fun e => core S H K family '' e.1)
  letI : Subsingleton (S ≃o S) := ⟨fun f g => by
    apply OrderIso.ext
    exact f.strictMono.eq_id.trans g.strictMono.eq_id.symm⟩
  have hCopies : Function.Injective (fun i : I => i.1.supportPiece) := by
    intro i j h
    have hRanges : Set.range i.1 = Set.range j.1 := congrArg HypergraphPiece.carrier h
    have hFun : i.1.toFun = j.1.toFun := (hMono i).eq_of_range_eq (hMono j) hRanges
    apply Subtype.ext
    rcases i with ⟨⟨f, _, _, _⟩, _⟩
    rcases j with ⟨⟨g, _, _, _⟩, _⟩
    change f = g at hFun
    cases hFun
    rfl
  obtain ⟨e₀, h₀, e₁, h₁, hNe⟩ := hTwo
  have hLocal : LocalForestThrough old m :=
    localForestThrough_mixedOwners_of_finiteMixed
      (fun i : I => i.1.supportPiece) Subtype.val hCopies Subtype.val_injective
      (strongSupportFamily_notIsOneEdge (fun i : I => i.1) e₀ e₁ h₀ h₁ hNe)
      _ m (fun i => Or.inl ⟨i.1, i.2, rfl⟩) (fun e => Or.inr ⟨e.1, e.2, rfl⟩)
      hMixed
  have hCore (a : I ⊕ K) (x : W) :
      core S H K family x ∈ (new a).carrier ↔ x ∈ (old a).carrier := by
    cases a with
    | inr E => exact (core S H K family).injective.mem_set_image
    | inl i =>
      change Sum.inl x ∈ Set.range (lift S H K family i) ↔ x ∈ Set.range i.1
      constructor
      · rintro ⟨y, hy⟩
        have hs : y ∈ S := RelStructure.Attachment.mem_of_copyMap_eq_inl hy
        rw [lift_mem S H K family i y hs] at hy
        exact ⟨⟨y, hs⟩, Sum.inl.inj hy⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y.1, lift_mem S H K family i y.1 y.2⟩
  have hPrivate (a : I ⊕ K) (i : I) (x : {x : V // x ∉ S})
      (h : Sum.inr (i, x) ∈ (new a).carrier) : a = .inl i := by
    cases a with
    | inr e =>
      obtain ⟨_, _, hEq⟩ := h
      cases hEq
    | inl j =>
      change Sum.inr (i, x) ∈ Set.range (lift S H K family j) at h
      obtain ⟨y, hy⟩ := h
      by_cases hs : y ∈ S
      · rw [lift_mem S H K family j y hs] at hy
        cases hy
      · rw [lift_not_mem S H K family j y hs] at hy
        exact congrArg Sum.inl (congrArg Prod.fst (Sum.inr.inj hy))
  have hEdges (a : I ⊕ K) :
      ((old a).map (core S H K family)).edges ⊆ (new a).edges := by
    rintro _ ⟨E, he, rfl⟩
    cases a with
    | inr f =>
      change E ∈ {f.1} at he
      obtain rfl := Set.mem_singleton_iff.mp he
      exact Set.mem_singleton _
    | inl i =>
      change E ∈ i.1.supportPiece.edges at he
      obtain ⟨_, ⟨e, he', rfl⟩, rfl⟩ := he
      exact ⟨e, he', (lift_image S H K family hSupport i he').symm⟩
  intro s hTest hCard
  let Q := {P : HypergraphPiece (Vertex S H K family) // P ∈ s}
  have hEvery (q : Q) : ∃ a : I ⊕ K, q.1 = new a := by
    rcases hTest q.1 q.2 with ⟨i, hi⟩ | ⟨_, ⟨e, he, rfl⟩, hE⟩
    · exact ⟨.inl i, hi⟩
    · exact ⟨.inr ⟨e, he⟩, hE⟩
  choose a ha using hEvery
  let idx : Q ↪ I ⊕ K := ⟨a, fun q r e => Subtype.ext
    ((ha q).trans ((congrArg new e).trans (ha r).symm))⟩
  have hForest := hLocal Q idx (by simpa [Q] using hCard)
  have hMapped := hForest.map (core S H K family)
  have hNew : ForestOfCopies (fun q : Q => new (a q)) := by
    apply hMapped.transfer_of_pair_intersections
    · rintro q _ ⟨x, hx, rfl⟩
      exact (hCore (a q) x).mpr hx
    · intro q r hNe
      ext z
      cases z with
      | inl x =>
        exact and_congr ((hCore (a q) x).trans
          ((core S H K family).injective.mem_set_image).symm)
          ((hCore (a r) x).trans
            ((core S H K family).injective.mem_set_image).symm)
      | inr p =>
        constructor
        · intro hz
          exact (hNe (idx.injective ((hPrivate _ p.1 p.2 hz.1).trans
            (hPrivate _ p.1 p.2 hz.2).symm))).elim
        · rintro ⟨⟨_, _, hx⟩, _⟩
          cases hx
    · exact fun q => hEdges (a q)
  have heq : (fun q : Q => new (a q)) = fun q : Q => q.1 :=
    funext fun q => (ha q).symm
  rwa [heq] at hNew

#print axioms StructuralRamsey.Girth.IsolatedRestoration.mixedForest
#print axioms StructuralRamsey.Girth.IsolatedRestoration.exists_order
#print axioms StructuralRamsey.Girth.IsolatedRestoration.strongLift_preserves_parts
#print axioms StructuralRamsey.Girth.IsolatedRestoration.edgeTransversal
#print axioms StructuralRamsey.Girth.IsolatedRestoration.girth_three
#print axioms StructuralRamsey.Girth.IsolatedRestoration.covered_and_arrow

end IsolatedRestoration
end StructuralRamsey.Girth
