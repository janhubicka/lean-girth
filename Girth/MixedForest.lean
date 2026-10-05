import Girth.SupportForestToTree

/-! # Mixed forests of A- and B-copies

The manuscript's forest-completion family contains both A-copies and B-copies.
This module packages one member uniformly, together with its relational carrier
and A-support hypergraph.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W ι : Type v}

/-- One member of a mixed family: either an ambient copy of A or an ambient
copy of B. -/
inductive ABMember
    (A : RelStructure L UA) (B : RelStructure L VB)
    (R : RelStructure L W) where
  | a (e : Embedding A R)
  | b (e : Embedding B R)

/-- Vertex type of the source structure represented by a mixed member. -/
def ABMember.VertexType
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W} :
    ABMember A B R → Type v
  | .a _ => UA
  | .b _ => VB

/-- Source structure represented by a mixed member. -/
def ABMember.source
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W} :
    (c : ABMember A B R) → RelStructure L c.VertexType
  | .a _ => A
  | .b _ => B

/-- Ambient embedding represented by a mixed member. -/
def ABMember.toAmbient
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W} :
    (c : ABMember A B R) → Embedding c.source R
  | .a e => e
  | .b e => e

/-- Carrier of a mixed member in the common ambient structure. -/
def ABMember.carrier
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    (c : ABMember A B R) : Set W :=
  Set.range c.toAmbient

/-- Realize either kind of member inside one copy of B.  An A-member uses the
fixed embedding A -> B; a B-member uses the identity. -/
def ABMember.toB
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    (c : ABMember A B R)
    (alphaB : Embedding A B) :
    Embedding c.source B := by
  cases c with
  | a _ => exact alphaB
  | b _ => exact (Iso.refl B).toEmbedding

/-- A-support piece of a mixed member.  An A-member is a one-edge piece; a
B-member carries all ambient A-copies contained in that B-copy. -/
def ABMember.supportPiece
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (c : ABMember A B R) : HypergraphPiece W := by
  cases c with
  | a e =>
      exact
        { carrier := copyCarrier e
          edges := {copyCarrier e}
          edge_subset_carrier := by
            intro edge he
            have hEq : edge = copyCarrier e := by simpa using he
            subst edge
            exact Set.Subset.rfl }
  | b e =>
      exact bSupportPiece A e

@[simp]
theorem ABMember.supportPiece_carrier
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (c : ABMember A B R) :
    (c.supportPiece A).carrier = c.carrier := by
  cases c <;> rfl

/-- Every support edge of a mixed member is the carrier of an ambient A-copy
contained in that member. -/
theorem ABMember.supportEdge_witness
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (c : ABMember A B R)
    {e : Set W}
    (he : e ∈ (c.supportPiece A).edges) :
    ∃ a : Embedding A R,
      copyCarrier a = e ∧ copyCarrier a ⊆ c.carrier := by
  cases c with
  | a f =>
      have hEq : e = copyCarrier f := by
        simpa [ABMember.supportPiece] using he
      subst e
      exact ⟨f, rfl, Set.Subset.rfl⟩
  | b f =>
      change
        ∃ a : Embedding A R,
          copyCarrier a = e ∧ copyCarrier a ⊆ copyCarrier f at he
      change
        ∃ a : Embedding A R,
          copyCarrier a = e ∧ copyCarrier a ⊆ copyCarrier f
      exact he

/-- A vertex is A-supported inside a mixed member.  For an A-member this is
automatic; for a B-member this is the manuscript's supported-singleton
condition. -/
def ABMember.VertexSupported
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (c : ABMember A B R) (x : W) : Prop :=
  ∃ a : Embedding A R,
    x ∈ copyCarrier a ∧ copyCarrier a ⊆ c.carrier

theorem ABMember.vertexSupported_of_mem_a
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (a : Embedding A R) {x : W}
    (hx : x ∈ copyCarrier a) :
    (ABMember.a a : ABMember A B R).VertexSupported A x :=
  ⟨a, hx, Set.Subset.rfl⟩

/-- Shared vertices are supported on both incident mixed members. -/
def PairwiseMixedSharedVerticesSupported
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (m : ι → ABMember A B R) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → ∀ ⦃x : W⦄,
    x ∈ (m i).carrier →
    x ∈ (m j).carrier →
      (m i).VertexSupported A x ∧
        (m j).VertexSupported A x

/-- Pairwise shared support is inherited after deleting one label. -/
theorem pairwiseMixedSharedVerticesSupported_erase
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    {m : ι → ABMember A B R}
    (h : PairwiseMixedSharedVerticesSupported A m)
    (leaf : ι) :
    PairwiseMixedSharedVerticesSupported A
      (fun j : {j : ι // j ≠ leaf} => m j.1) := by
  intro i j hij x hxi hxj
  apply h
  · intro hval
    apply hij
    exact Subtype.ext hval
  · exact hxi
  · exact hxj

end StructuralRamsey.Girth
