import Girth.TrainFillingIndexedChoiceCore
import Girth.TrainFillingSelectedEdgeRange

set_option Elab.async false

/-!
# Actual contracted G0 edge carriers are distinct

The heterogeneous choice union G0 has vertex type Σ c, (U c).Vertex.
Its contracted first-wagon physical edges are indexed by (choice c, old
first-wagon p) and have full carriers equal to the image of X under
the genuine private-extension placement, with the choice tag retained.

Different choices have different vertex tags. Inside one choice, first-
wagon linearity and at least two local template vertices exclude equal
carriers of two different first wagons. Consequently the contracted
edge carrier map is injective, not an assumption on a prospective M.

Given a selected vertex embedding of this genuine G0 contracted source
into N that sends every whole first wagon onto an actual old N edge,
the selected old physical-edge embedding is now constructed directly.
Neither output M-copy existence nor actual proper-cut relation reflection
or final cutoff-two Ramsey arrow is claimed.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Y : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- A physical contracted edge has its COMPLETE first-wagon carrier,
not merely the selected W* edge subset inside that wagon. -/
def contractedCarrier (e : C × P) : Set (Vertex U) :=
  (tagVertex U e.1) '' Set.range ((U e.1).place e.2)

/-- The contracted first-wagon edge carrier stays in its own
choice component, with all other choices completely disjoint. -/
theorem contractedCarrier_subset_component (e : C × P) :
    contractedCarrier U e ⊆ componentCarrier U e.1 := by
  rintro z ⟨w, _hw, rfl⟩
  exact ⟨w, rfl⟩

/-- The whole contracted heterogeneous G0 is a LINEAR physical
hypergraph whenever each choice's old first wagons form a linear family.
No two-vertex hypothesis is needed for linearity itself; it is needed
only to rule out duplicate contracted edge carriers. -/
theorem contractedCarrier_linear
    (hOld : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton) :
    ∀ e f : C × P, e ≠ f →
      (contractedCarrier U e ∩ contractedCarrier U f).Subsingleton := by
  rintro ⟨c, p⟩ ⟨d, q⟩ hef
  by_cases hcd : c = d
  · subst d
    have hpq : p ≠ q := by
      intro h
      exact hef (congrArg (Prod.mk c) h)
    have hSmall : (Set.range ((U c).place p) ∩
        Set.range ((U c).place q)).Subsingleton :=
      (U c).ranges_inter_subsingleton (hOld c) p q hpq
    intro z hz w hw
    obtain ⟨x, hx, hxz⟩ := hz.1
    obtain ⟨y, hy, hyz⟩ := hz.2
    have hxy : x = y := (tagVertex_injective U c) (hxz.trans hyz.symm)
    subst y
    obtain ⟨u, hu, huw⟩ := hw.1
    obtain ⟨v, hv, hvw⟩ := hw.2
    have huv : u = v := (tagVertex_injective U c) (huw.trans hvw.symm)
    subst v
    have hxu : x = u := hSmall ⟨hx, hy⟩ ⟨hu, hv⟩
    calc
      z = tagVertex U c x := hxz.symm
      _ = tagVertex U c u := congrArg (tagVertex U c) hxu
      _ = w := huw
  · intro z hz w hw
    have hc : z ∈ componentCarrier U c :=
      U.contractedCarrier_subset_component (c, p) hz.1
    have hd : z ∈ componentCarrier U d :=
      U.contractedCarrier_subset_component (d, q) hz.2
    exact False.elim ((Set.disjoint_left.mp
      (componentCarrier_disjoint U c d hcd)) hc hd)

/-- The actual contracted edge carriers are physically distinct.

Nontriviality of X is essential: a single-vertex X would allow distinct
first wagons to have the same singleton carrier even in a linear train.
The local old-wagon intersection hypothesis is the ordinary first-wagon
linearity of G0; it is not an output realization assumption. -/
theorem contractedCarrier_injective [Nontrivial X]
    (hOld : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton) :
    Function.Injective (contractedCarrier U) := by
  rintro ⟨c, p⟩ ⟨d, q⟩ hEq
  have hcd : c = d := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hz : tagVertex U c ((U c).place p x) ∈
        contractedCarrier U (c, p) :=
      ⟨(U c).place p x, ⟨x, rfl⟩, rfl⟩
    rw [hEq] at hz
    obtain ⟨z, _hz, hzEq⟩ := hz
    exact (congrArg Sigma.fst hzEq).symm
  subst d
  have hRange : Set.range ((U c).place p) =
      Set.range ((U c).place q) := by
    ext z
    constructor
    · intro hz
      have hTag : tagVertex U c z ∈ contractedCarrier U (c, p) :=
        ⟨z, hz, rfl⟩
      rw [hEq] at hTag
      obtain ⟨w, hw, hwz⟩ := hTag
      have hzw : w = z := (tagVertex_injective U c) hwz
      simpa only [hzw] using hw
    · intro hz
      have hTag : tagVertex U c z ∈ contractedCarrier U (c, q) :=
        ⟨z, hz, rfl⟩
      rw [← hEq] at hTag
      obtain ⟨w, hw, hwz⟩ := hTag
      have hzw : w = z := (tagVertex_injective U c) hwz
      simpa only [hzw] using hw
  have hpq : p = q := by
    by_contra hpq
    have hSmall : (Set.range ((U c).place p) ∩
        Set.range ((U c).place q)).Subsingleton :=
      (U c).ranges_inter_subsingleton (hOld c) p q hpq
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    have hxP : (U c).place p x ∈ Set.range ((U c).place p) := ⟨x, rfl⟩
    have hyP : (U c).place p y ∈ Set.range ((U c).place p) := ⟨y, rfl⟩
    have hxQ : (U c).place p x ∈ Set.range ((U c).place q) := by
      rw [← hRange]
      exact hxP
    have hyQ : (U c).place p y ∈ Set.range ((U c).place q) := by
      rw [← hRange]
      exact hyP
    have hxyPlace : (U c).place p x = (U c).place p y :=
      hSmall ⟨hxP, hxQ⟩ ⟨hyP, hyQ⟩
    exact hxy ((U c).place_injective p hxyPlace)
  exact congrArg (Prod.mk c) hpq

/-- The actual selected M-copy vertex embedding alone constructs the
corresponding physical old-edge embedding, once it maps each whole
contracted source carrier onto an old N-edge. No independent physical
edge map, carrier equality, or injectivity are supplied. -/
def contractedOldEdgeEmbedding
    [Nontrivial X]
    (hOld : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (F : UniformFillingData Y X)
    (vertex : Vertex U ↪ Y)
    (hImage : ∀ e : C × P,
      vertex '' contractedCarrier U e ∈ F.oldEdges) :
    (C × P) ↪ F.OldEdge :=
  F.oldEdgeEmbedding_of_exact_carriers (contractedCarrier U)
    (contractedCarrier_injective U hOld) vertex
    (fun e => (⟨vertex '' contractedCarrier U e, hImage e⟩ : F.OldEdge))
    (fun _ => rfl)

/-- Every constructed contracted old edge is literally the image of
its full first-wagon carrier under the selected vertex embedding. -/
@[simp] theorem contractedOldEdgeEmbedding_carrier
    [Nontrivial X]
    (hOld : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (F : UniformFillingData Y X)
    (vertex : Vertex U ↪ Y)
    (hImage : ∀ e : C × P,
      vertex '' contractedCarrier U e ∈ F.oldEdges)
    (e : C × P) :
    (contractedOldEdgeEmbedding U hOld F vertex hImage e).1 =
      vertex '' contractedCarrier U e := rfl

end StructuralRamsey.Girth.IndexedPrivateChoice
