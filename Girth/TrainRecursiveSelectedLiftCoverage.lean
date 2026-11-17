import Girth.SelectedRelationalLiftUnion
import Girth.TrainRecursiveCoveredClosureClass

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {U V W X I : Type v}
variable {A : RelStructure L U} {B : RelStructure L V} {D : RelStructure L W}

/-- Coverage of a lifted irreducible is witnessed by a selected copy and
an actual A-copy in the target. Two lifts of the same original A-embedding
must agree, as they do when shared edge vertices have canonical tags. -/
theorem selectedRelationalLiftUnion_covered_of_compatible
    (original : I → Embedding B D) (lift : I → V ↪ X) (project : X → W)
    (hProject : ∀ i x, project (lift i x) = original i x)
    (hStrong : ∀ i, AStrong A D (copyCarrier (original i)))
    (hCoverage : NonsingletonIrreduciblesExtendTo A D)
    (hCompatible : ∀ i j (a b : Embedding A B),
      (original i).comp a = (original j).comp b →
      (lift i : V → X) ∘ a = (lift j : V → X) ∘ b)
    (S : Set X) (hS : ((selectedRelationalLiftUnion B lift).induce S).Irreducible)
    (hLarge : ¬ S.Subsingleton) :
    ∃ (i : I) (a : Embedding A B), S ⊆
      copyCarrier ((selectedRelationalLiftUnionEmbedding original lift project hProject i).comp a) := by
  classical
  let C := selectedRelationalLiftUnion B lift
  let f (i : I) := selectedRelationalLiftUnionEmbedding original lift project hProject i
  have hTogether (x y : S) (hxy : x ≠ y) :
      ∃ (i : I) (p q : V), lift i p = x.1 ∧ lift i q = y.1 := by
    obtain ⟨R, t, k, l, ht, hk, hl⟩ := hS hxy
    obtain ⟨i, s, _, hs⟩ := ht
    exact ⟨i, s k, s l,
      (congrFun hs k).trans (congrArg Subtype.val hk),
      (congrFun hs l).trans (congrArg Subtype.val hl)⟩
  have hInjective (x y : S) (h : project x.1 = project y.1) : x = y := by
    by_contra hne
    obtain ⟨i, p, q, hp, hq⟩ := hTogether x y hne
    have hpq : original i p = original i q :=
      (hProject i p).symm.trans ((congrArg project hp).trans
        (h.trans ((congrArg project hq).symm.trans (hProject i q))))
    apply hne
    apply Subtype.ext
    exact hp.symm.trans ((congrArg (lift i) ((original i).injective hpq)).trans hq)
  let T := project '' S
  have hHom : C.IsHomomorphism D project := by
    intro R z
    rintro ⟨i, t, ht, hEq⟩
    have hEq' : (original i : V → W) ∘ t = project ∘ z := by
      funext k
      exact (hProject i (t k)).symm.trans (congrArg project (congrFun hEq k))
    rw [← hEq']
    exact ((original i).map_rel_iff R t).mpr ht
  have hT : (D.induce T).Irreducible := by
    intro x y hxy
    obtain ⟨x', hx', hx⟩ := x.2
    obtain ⟨y', hy', hy⟩ := y.2
    have hne : (⟨x', hx'⟩ : S) ≠ ⟨y', hy'⟩ := by
      intro h
      apply hxy
      exact Subtype.ext (hx.symm.trans ((congrArg (fun z : S => project z.1) h).trans hy))
    obtain ⟨R, t, k, l, ht, hk, hl⟩ := hS hne
    refine ⟨R, fun j => ⟨project (t j).1, ⟨(t j).1, (t j).2, rfl⟩⟩,
      k, l, hHom R (Subtype.val ∘ t) ht, ?_, ?_⟩
    · exact Subtype.ext ((congrArg (fun z : S => project z.1) hk).trans hx)
    · exact Subtype.ext ((congrArg (fun z : S => project z.1) hl).trans hy)
  have hTLarge : ¬ T.Subsingleton := by
    intro h
    apply hLarge
    intro x hx y hy
    exact congrArg Subtype.val (hInjective ⟨x, hx⟩ ⟨y, hy⟩
      (h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩))
  obtain ⟨e, he⟩ := hCoverage T hT hTLarge
  have hPair (x y : S) (hxy : x ≠ y) :
      ∃ (i : I) (a : Embedding A B), (original i).comp a = e ∧
        x.1 ∈ copyCarrier ((f i).comp a) ∧ y.1 ∈ copyCarrier ((f i).comp a) := by
    obtain ⟨i, p, q, hp, hq⟩ := hTogether x y hxy
    have hpx : project x.1 = original i p :=
      (congrArg project hp).symm.trans (hProject i p)
    have hpy : project y.1 = original i q :=
      (congrArg project hq).symm.trans (hProject i q)
    have hIn (z : S) : project z.1 ∈ copyCarrier e := he ⟨z.1, z.2, rfl⟩
    have hInter : ¬ (copyCarrier e ∩ copyCarrier (original i)).Subsingleton := by
      intro h
      exact hxy (hInjective x y (h ⟨hIn x, ⟨p, hpx.symm⟩⟩ ⟨hIn y, ⟨q, hpy.symm⟩⟩))
    have hFactor (w : U) : ∃ b : V, e w = original i b := by
      obtain ⟨b, hb⟩ := hStrong i e hInter ⟨w, rfl⟩
      exact ⟨b, hb.symm⟩
    let a := e.factorThroughRange (original i) hFactor
    have ha (w : U) : e w = original i (a w) := Classical.choose_spec (hFactor w)
    have hCover (z : S) (r : V) (hr : lift i r = z.1)
        (hpr : project z.1 = original i r) :
        z.1 ∈ copyCarrier ((f i).comp a) := by
      obtain ⟨w, hw⟩ := hIn z
      have hwa : a w = r := (original i).injective ((ha w).symm.trans (hw.trans hpr))
      exact ⟨w, (congrArg (lift i) hwa).trans hr⟩
    exact ⟨i, a, Embedding.ext (fun w => (ha w).symm), hCover x p hp hpx,
      hCover y q hq hpy⟩
  rw [Set.not_subsingleton_iff] at hLarge
  obtain ⟨x, hx, y, hy, hxy⟩ := hLarge
  let x' : S := ⟨x, hx⟩
  let y' : S := ⟨y, hy⟩
  obtain ⟨i, a, ha, hix, _⟩ :=
    hPair x' y' (fun h => hxy (congrArg Subtype.val h))
  refine ⟨i, a, ?_⟩
  intro z hz
  let z' : S := ⟨z, hz⟩
  by_cases hEqual : z' = x'
  · rw [show z = x from congrArg Subtype.val hEqual]
    exact hix
  · obtain ⟨j, b, hb, hjz, _⟩ := hPair z' x' hEqual
    have hLift : (f i).comp a = (f j).comp b := by
      apply Embedding.ext
      intro u
      exact congrFun (hCompatible i j a b (ha.trans hb.symm)) u
    rw [hLift]
    exact hjz

/-- Isolated ambient vertices are excluded by using only the selected lift
carriers. If the target vertices lie on A-copies, singleton and empty
irreducibles also extend to an A-copy in an actual selected lift. -/
theorem selectedRelationalLiftUnion_all_irreducibles_covered
    (original : I → Embedding B D) (lift : I → V ↪ X) (project : X → W)
    (hProject : ∀ i x, project (lift i x) = original i x)
    (hStrong : ∀ i, AStrong A D (copyCarrier (original i)))
    (hCoverage : NonsingletonIrreduciblesExtendTo A D)
    (hCompatible : ∀ i j (a b : Embedding A B),
      (original i).comp a = (original j).comp b →
      (lift i : V → X) ∘ a = (lift j : V → X) ∘ b)
    (hVertex : ∀ x : X, ∃ i : I, x ∈ Set.range (lift i))
    (hTargetVertex : ∀ x : V, ∃ a : Embedding A B, x ∈ copyCarrier a)
    (hNonempty : Nonempty I) (hTargetEdge : Nonempty (Embedding A B))
    (S : Set X) (hS : ((selectedRelationalLiftUnion B lift).induce S).Irreducible) :
    ∃ (i : I) (a : Embedding A B), S ⊆
      copyCarrier ((selectedRelationalLiftUnionEmbedding original lift project hProject i).comp a) := by
  classical
  by_cases hSmall : S.Subsingleton
  · by_cases hN : S.Nonempty
    · obtain ⟨x, hx⟩ := hN
      obtain ⟨i, v, hv⟩ := hVertex x
      obtain ⟨a, u, hu⟩ := hTargetVertex v
      refine ⟨i, a, ?_⟩
      intro z hz
      exact ⟨u, (congrArg (lift i) hu).trans (hv.trans (hSmall hx hz))⟩
    · obtain ⟨i⟩ := hNonempty
      obtain ⟨a⟩ := hTargetEdge
      exact ⟨i, a, fun _ hx => (hN ⟨_, hx⟩).elim⟩
  · exact selectedRelationalLiftUnion_covered_of_compatible
      original lift project hProject hStrong hCoverage hCompatible S hS hSmall

end StructuralRamsey.Girth
