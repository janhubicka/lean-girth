import Girth.TrainFillingSparseFirstWagon
import Girth.TrainFillingPrivateRealUnionLocalCoverage
import Girth.TrainFillingContractFirstTrain
import Girth.TrainFillingPrivateActualFirstParameter
import Girth.TrainEndpointGeometry
import Girth.TrainFillingPrivateActualWagonOwner

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v
variable {K : RelLanguage.{u}} {A V P : Type v}
variable (Small : RelStructure K A) (Target : System K A V) (carrier : P → Set V)

local notation "W" => firstWagonSparseSystem Target carrier

/-- Relations of arity zero have the same value in every induced first
wagon. Thus the literal tags give induced maps for the full language. -/
def firstWagonSparseSummand (p : P) :
    Embedding (Target.toRelStructure.induce (carrier p)) (W).toRelStructure where
  toFun x := ⟨p, x⟩
  injective := by
    intro x y h
    exact Subtype.ext (congrArg (fun w : FirstWagonUnionVertex carrier => w.2.1) h)
  map_rel_iff := by
    intro r z
    constructor
    · rintro ⟨q, w, hEntry, hw⟩
      by_cases hPositive : 0 < K.arity r
      · have hpq : p = q := congrArg Sigma.fst (hEntry ⟨0, hPositive⟩)
        subst q
        have hEq : w = z := by
          funext i
          apply Subtype.ext
          exact (congrArg (fun x : FirstWagonUnionVertex carrier => x.2.1) (hEntry i)).symm
        exact hEq ▸ hw
      · have hEq : Subtype.val ∘ w = Subtype.val ∘ z := by
          funext i
          exact (hPositive (Nat.zero_lt_of_lt i.isLt)).elim
        change Target.rel r (Subtype.val ∘ w) at hw
        change Target.rel r (Subtype.val ∘ z)
        exact hEq ▸ hw
    · intro hz
      exact ⟨p, z, fun _ => rfl, hz⟩

theorem firstWagonSparseSystem_projects
    (hProjection : Target.toRelStructure.IsHomomorphism Small Target.part) :
    (W).toRelStructure.IsHomomorphism Small (W).part := by
  intro r z hz
  obtain ⟨p, w, hEntry, hw⟩ := hz
  have hEq : (W).part ∘ z = Target.part ∘ Subtype.val ∘ w := by
    funext i
    exact congrArg (W).part (hEntry i)
  rw [hEq]
  exact hProjection r (Subtype.val ∘ w) hw

/-- A spanning related tuple puts any sparse A-copy in a single genuine
tagged wagon, even in a language containing unrelated nullary symbols. -/
theorem firstWagonSparseCopy_inside
    (hSpanning : HasSpanningRelation Small)
    (a : Embedding Small (W).toRelStructure) :
    ∃ p : P, copyCarrier a ⊆ copyCarrier (firstWagonSparseSummand Target carrier p) := by
  obtain ⟨r, z, hz, hSpan⟩ := hSpanning
  obtain ⟨p, w, hEntry, _⟩ := (a.map_rel_iff r z).mpr hz
  refine ⟨p, ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, rfl⟩ := hSpan x
  exact ⟨w i, (hEntry i).symm⟩

theorem firstWagonSparseSummand_aStrong
    (hSpanning : HasSpanningRelation Small) (p : P) :
    AStrong Small (W).toRelStructure (copyCarrier (firstWagonSparseSummand Target carrier p)) := by
  intro a hMeet
  obtain ⟨q, hInside⟩ := firstWagonSparseCopy_inside Small Target carrier hSpanning a
  obtain ⟨x, hx, _⟩ := Set.not_subsingleton_iff.mp hMeet
  obtain ⟨u, hu⟩ := hInside hx.1
  obtain ⟨v, hv⟩ := hx.2
  have hqp : q = p := congrArg Sigma.fst (hu.trans hv.symm)
  exact hqp ▸ hInside

theorem firstWagonSparseSystem_covered
    (hLocalCover : ∀ p (x : {v : V // v ∈ carrier p}),
      ∃ a : Embedding Small (Target.toRelStructure.induce (carrier p)), x ∈ copyCarrier a) :
    ∀ x, ∃ a : Embedding Small (W).toRelStructure, x ∈ copyCarrier a := by
  rintro ⟨p, x⟩
  obtain ⟨a, u, rfl⟩ := hLocalCover p x
  exact ⟨(firstWagonSparseSummand Target carrier p).comp a, u, rfl⟩

theorem firstWagonSparseSystem_fineEdges
    (hSpanning : HasSpanningRelation Small)
    (hTargetFine : ∀ (a : Embedding Small Target.toRelStructure) x, Target.part (a x) = x)
    (a : Embedding Small (W).toRelStructure) (x : A) : (W).part (a x) = x := by
  obtain ⟨p, hp⟩ := firstWagonSparseCopy_inside Small Target carrier hSpanning a
  let s := firstWagonSparseSummand Target carrier p
  have hRange (u : A) : ∃ v : {v : V // v ∈ carrier p}, a u = s v := by
    obtain ⟨v, hv⟩ := hp (show a u ∈ copyCarrier a from ⟨u, rfl⟩)
    exact ⟨v, hv.symm⟩
  let b := a.factorThroughRange s hRange
  have hApply : a x = s (b x) := Classical.choose_spec (hRange x)
  rw [hApply]
  exact hTargetFine ((RelStructure.inclusion Target.toRelStructure (carrier p)).comp b) x

/-- The full support of the sparse wagon union, including all original
symbols, is exactly the tagged original physical edges. -/
theorem firstWagonSparseSystem_support_eq_tagged_of_spanning
    (hSpanning : HasSpanningRelation Small) :
    supportCopies Small (W).toRelStructure =
      taggedFirstWagonEdges carrier (supportCopies Small Target.toRelStructure) := by
  ext e
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨p, hp⟩ := firstWagonSparseCopy_inside Small Target carrier hSpanning a
    let s := firstWagonSparseSummand Target carrier p
    let inc := RelStructure.inclusion Target.toRelStructure (carrier p)
    have hRange (x : A) : ∃ y : {v : V // v ∈ carrier p}, a x = s y := by
      obtain ⟨y, hy⟩ := hp (show a x ∈ copyCarrier a from ⟨x, rfl⟩)
      exact ⟨y, hy.symm⟩
    let b := a.factorThroughRange s hRange
    have hComp : s.comp b = a :=
      Embedding.ext (fun x => (Classical.choose_spec (hRange x)).symm)
    refine ⟨p, copyCarrier b, ⟨inc.comp b, ?_⟩, ?_⟩
    · exact (UniformPrivateTemplate.image_copyCarrier_comp Small
        (Target.toRelStructure.induce (carrier p)) Target.toRelStructure inc b)
    · rw [← hComp]
      exact (UniformPrivateTemplate.image_copyCarrier_comp Small
        (Target.toRelStructure.induce (carrier p)) (W).toRelStructure s b).symm
  · rintro ⟨p, f, ⟨a, ha⟩, rfl⟩
    let inc := RelStructure.inclusion Target.toRelStructure (carrier p)
    let s := firstWagonSparseSummand Target carrier p
    have hRange (x : A) : ∃ y : {v : V // v ∈ carrier p}, a x = inc y := by
      have hx : a x ∈ Subtype.val '' f := ha.symm ▸ (show a x ∈ copyCarrier a from ⟨x, rfl⟩)
      obtain ⟨y, _, hy⟩ := hx
      exact ⟨y, hy.symm⟩
    let b := a.factorThroughRange inc hRange
    have hComp : inc.comp b = a :=
      Embedding.ext (fun x => (Classical.choose_spec (hRange x)).symm)
    have hCarrier : f = copyCarrier b := by
      apply Set.image_injective.mpr Subtype.val_injective
      exact ha.trans ((congrArg copyCarrier hComp.symm).trans
        (UniformPrivateTemplate.image_copyCarrier_comp Small
          (Target.toRelStructure.induce (carrier p)) Target.toRelStructure inc b).symm)
    refine ⟨s.comp b, ?_⟩
    rw [hCarrier]
    exact (UniformPrivateTemplate.image_copyCarrier_comp Small
      (Target.toRelStructure.induce (carrier p)) (W).toRelStructure s b)

section Contact

variable {E : Set (Set V)} {carrier : P → Set V}
variable {e f : Set (FirstWagonUnionVertex carrier)}

/-- Intersecting tagged edges have distinct original edges in the same
summand. Every contact projects literally to their original contact. -/
theorem taggedFirstWagon_intersection
    (he : e ∈ taggedFirstWagonEdges carrier E)
    (hf : f ∈ taggedFirstWagonEdges carrier E)
    (hne : e ≠ f) (z : FirstWagonUnionVertex carrier) (hz : z ∈ e ∩ f) :
    ∃ (p : P) (a b : {s : Set V // s ∈ E}), a ≠ b ∧
      a.1 ⊆ carrier p ∧ b.1 ⊆ carrier p ∧
      ∀ x ∈ e ∩ f, x.1 = p ∧ x.2.1 ∈ a.1 ∩ b.1 := by
  obtain ⟨p, pe, hpe, rfl⟩ := he
  obtain ⟨q, qf, hqf, rfl⟩ := hf
  obtain ⟨u, _, hu⟩ := hz.1
  obtain ⟨v, _, hv⟩ := hz.2
  have hpq : p = q := congrArg Sigma.fst (hu.trans hv.symm)
  subst q
  refine ⟨p, ⟨Subtype.val '' pe, hpe⟩, ⟨Subtype.val '' qf, hqf⟩, ?_, ?_, ?_, ?_⟩
  · intro hEq
    have hImages : Subtype.val '' pe = Subtype.val '' qf :=
      congrArg (fun a : {s : Set V // s ∈ E} => a.1) hEq
    have hSets : pe = qf := Set.image_injective.mpr Subtype.val_injective hImages
    exact hne (congrArg (fun set => (fun x => (⟨p, x⟩ : FirstWagonUnionVertex carrier)) '' set) hSets)
  · rintro _ ⟨u, _, rfl⟩
    exact u.2
  · rintro _ ⟨u, _, rfl⟩
    exact u.2
  · intro x hx
    obtain ⟨u, hu, hux⟩ := hx.1
    obtain ⟨v, hv, hvx⟩ := hx.2
    refine ⟨(congrArg Sigma.fst hux).symm, ⟨u, hu, ?_⟩, ⟨v, hv, ?_⟩⟩
    · exact congrArg (fun w : FirstWagonUnionVertex carrier => w.2.1) hux
    · exact congrArg (fun w : FirstWagonUnionVertex carrier => w.2.1) hvx

theorem taggedFirstWagonEdges_pairwise_subsingleton
    (hLinear : ∀ a b : {s : Set V // s ∈ E}, a ≠ b → (a.1 ∩ b.1).Subsingleton) :
    ∀ a b : {s : Set (FirstWagonUnionVertex carrier) // s ∈ taggedFirstWagonEdges carrier E},
      a ≠ b → (a.1 ∩ b.1).Subsingleton := by
  intro a b hne x hx y hy
  obtain ⟨p, e, f, hef, _, _, hInter⟩ :=
    taggedFirstWagon_intersection a.2 b.2 (fun h => hne (Subtype.ext h)) x hx
  obtain ⟨hxPart, hxV⟩ := hInter x hx
  obtain ⟨hyPart, hyV⟩ := hInter y hy
  have hV := hLinear e f hef hxV hyV
  rcases x with ⟨p₁, x⟩
  rcases y with ⟨p₂, y⟩
  change p₁ = p at hxPart
  change p₂ = p at hyPart
  subst p₁
  subst p₂
  exact congrArg (fun z => (⟨p, z⟩ : FirstWagonUnionVertex carrier)) (Subtype.ext hV)

end Contact

/-- The first parameter of the actual train is the allowed predicate
condition on its sparse disjoint first-wagon union. -/
theorem firstWagonSparseSystem_marked
    [Nontrivial A] {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge Small Target.toRelStructure) (m + 1))
    (hSpanning : HasSpanningRelation Small)
    (hLinear : ∀ p q : T.FirstWagon, p ≠ q →
      (T.wagonClassCarrier Subtype.val (0 : Fin (m + 1)).succ p ∩
        T.wagonClassCarrier Subtype.val (0 : Fin (m + 1)).succ q).Subsingleton)
    (allowed : Set A)
    (hParameter : TrainParentIntersectionBound
      (T.wagonClassCarrier Subtype.val 0)
      (T.wagonParent 0 (0 : Fin (m + 1)).succ (by change (0 : ℕ) ≤ _; omega))
      (Target.part ⁻¹' allowed)) :
    let wagon := T.wagonClassCarrier Subtype.val (0 : Fin (m + 1)).succ
    let sparse := firstWagonSparseSystem Target wagon
    ∀ e f : Set (FirstWagonUnionVertex wagon),
      e ∈ supportCopies Small sparse.toRelStructure → f ∈ supportCopies Small sparse.toRelStructure →
      e ≠ f → ∀ z : FirstWagonUnionVertex wagon, z ∈ e → z ∈ f → sparse.part z ∈ allowed := by
  dsimp only
  classical
  let wagon := T.wagonClassCarrier Subtype.val (0 : Fin (m + 1)).succ
  let sparse := firstWagonSparseSystem Target wagon
  have hExact := firstWagonSparseSystem_support_eq_tagged_of_spanning Small Target wagon hSpanning
  intro e f he hf hne z hze hzf
  change e ∈ supportCopies Small sparse.toRelStructure at he
  change f ∈ supportCopies Small sparse.toRelStructure at hf
  rw [hExact] at he hf
  obtain ⟨p, a, b, hab, ha, hb, hTrace⟩ :=
    taggedFirstWagon_intersection he hf hne z ⟨hze, hzf⟩
  have hOwner (e : OldACarrierEdge Small Target.toRelStructure) (he : e.1 ⊆ wagon p) :
      T.firstWagon e = p := by
    by_contra hNe
    have hSub := hLinear (T.firstWagon e) p hNe
    have hIn : e.1 ⊆ wagon (T.firstWagon e) :=
      T.edge_subset_ownerWagonCarrier Subtype.val (0 : Fin (m + 1)).succ e
    obtain ⟨a, ha⟩ := e.2
    obtain ⟨u, v, hUV⟩ := exists_pair_ne A
    have hu : a u ∈ e.1 := ha.symm ▸ (show a u ∈ copyCarrier a from ⟨u, rfl⟩)
    have hv : a v ∈ e.1 := ha.symm ▸ (show a v ∈ copyCarrier a from ⟨v, rfl⟩)
    exact hUV (a.injective (hSub ⟨hIn hu, he hu⟩ ⟨hIn hv, he hv⟩))
  have hSame : T.rel (0 : Fin (m + 1)).succ a b :=
    Quotient.exact ((hOwner a ha).trans (hOwner b hb).symm)
  exact T.firstParameter_physicalEdge_inter_allowed Subtype.val
    (0 : Fin (m + 1)).succ (Target.part ⁻¹' allowed) hParameter a b hab hSame
    (hTrace z ⟨hze, hzf⟩).2

end StructuralRamsey.Girth
