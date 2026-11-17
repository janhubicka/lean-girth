import Girth.SupportedTree
import PartiteConstruction.Relational.Order

/-!
# Forgetting the order in a supported tree amalgam

Induced embeddings and concrete free amalgamation diagrams restrict to
the original language. The overlap with a supporting A-copy uses the
same underlying map, including for the supported-point constructor.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V W X : Type v}

/-- Restrict an induced embedding to the unordered relations. -/
def Embedding.orderReduct
    {A : RelStructure L.withOrder U} {B : RelStructure L.withOrder V}
    (f : Embedding A B) : Embedding A.orderReduct B.orderReduct where
  toFun := f
  injective := f.injective
  map_rel_iff r t := f.map_rel_iff (.inl r) t

/-- Restrict an isomorphism to the unordered relations. -/
def Iso.orderReduct
    {A : RelStructure L.withOrder U} {B : RelStructure L.withOrder V}
    (f : Iso A B) : Iso A.orderReduct B.orderReduct where
  toEquiv := f.toEquiv
  map_rel_iff r t := f.map_rel_iff (.inl r) t

/-- The same vertex overlap and free tuple union remain after forgetting order. -/
theorem IsFreeAmalgam.orderReduct
    {D : RelStructure L.withOrder U} {A : RelStructure L.withOrder V}
    {B : RelStructure L.withOrder W} {T : RelStructure L.withOrder X}
    {fA : Embedding D A} {fB : Embedding D B}
    {iA : Embedding A T} {iB : Embedding B T}
    (h : IsFreeAmalgam fA fB iA iB) :
    IsFreeAmalgam fA.orderReduct fB.orderReduct iA.orderReduct iB.orderReduct :=
  ⟨h.covers, h.overlap, fun r t => h.rel_iff (.inl r) t⟩

end StructuralRamsey.RelStructure

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V W : Type v}

/-- The order reduct of an A-supported tree amalgam is the corresponding
supported tree amalgam of the reducts with the same two overlap types. -/
theorem ASupportedTreeAmalgam.orderReduct
    {A : RelStructure L.withOrder U} {B : RelStructure L.withOrder V}
    {T : RelStructure L.withOrder W}
    (hT : ASupportedTreeAmalgam A B W T) :
    ASupportedTreeAmalgam A.orderReduct B.orderReduct W T.orderReduct := by
  induction hT with
  | copy h =>
    exact .copy h.orderReduct
  | glueA _ f₀ fB i₀ iB hfree ih =>
    exact .glueA ih f₀.orderReduct fB.orderReduct i₀.orderReduct iB.orderReduct hfree.orderReduct
  | gluePoint _ f₀ fB support₀ supportB i₀ iB hfree ih =>
    obtain ⟨a₀, ha₀⟩ := support₀
    obtain ⟨aB, haB⟩ := supportB
    exact .gluePoint ih f₀.orderReduct fB.orderReduct
      ⟨a₀.orderReduct, ha₀⟩ ⟨aB.orderReduct, haB⟩
      i₀.orderReduct iB.orderReduct hfree.orderReduct

/-- Induced small-structure embeddings survive forgetting order, as do
the support constraints on the receiving tree amalgam. -/
theorem smallInducedStructure_orderReduct
    {A : RelStructure L.withOrder U} {B : RelStructure L.withOrder V}
    {C : RelStructure L.withOrder W} {Z : Set W}
    (h : ∃ (Y : Type v) (T : RelStructure L.withOrder Y) (_ : Embedding (C.induce Z) T),
      ASupportedTreeAmalgam A B Y T) :
    ∃ (Y : Type v) (T : RelStructure L Y) (_ : Embedding (C.orderReduct.induce Z) T),
      ASupportedTreeAmalgam A.orderReduct B.orderReduct Y T := by
  obtain ⟨Y, T, e, hT⟩ := h
  exact ⟨Y, T.orderReduct, e.orderReduct, hT.orderReduct⟩

end StructuralRamsey.Girth
