import Girth.DesignatedPicture
import PartiteConstruction.Partite.Induced
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Coarsen a large Ramsey-base partition to the actual A-parts

A selected-copy label in the lower forest recursion projects by an INJECTIVE
base embedding.  In a nontrivial A-partite source, the actual A-part map is
NOT injective.  Hence using the A-vertex type itself as the selected-copy
base cannot work (#765/#768).

The correct conditional interface uses a LARGER Q-partite base D, whose
vertex type P can represent every target vertex injectively, and a
P-partite witness E over D.toRelStructure.  Compose E.part : X -> P
with D.part : P -> Q. The resulting Q-partite witness has EXACTLY the
same relational structure, vertices, edges, and copies.  Transversality
follows because the old projection sends E-relations to genuine
D-relations and D itself is Q-transversal.

If the selected copy's base embedding preserves the Q-parts of the
target, the very same selected relational embedding becomes a genuine
Q-PARTITE gluing embedding after coarsening.  This avoids treating an
injective selected-copy base projection as the noninjective A-part map.

The construction and arrow remain conditional: the actual lower
Ramsey witness, its correct base family and positive system-girth
certificates, and the attached-output supreme-cycle transfer are
separate obligations. No appendix or final forest theorem is claimed.
-/

namespace StructuralRamsey.Partite

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {P Q X Y : Type v}

/-- Coarsen the witness's PARTITION, not its relational or physical
edge structure. The target base D must be a Q-partite system and E's
projection to its relational reduct must preserve relations. -/
def System.coarsenVia (D : System L Q P) (E : System L P X)
    (hE : E.IsPartiteOver D.toRelStructure) : System L Q X where
  toRelStructure := E.toRelStructure
  part x := D.part (E.part x)
  transversal := by
    intro R x hx i j hSame
    have hDRel : D.rel R (E.part ∘ x) := hE.1 R x hx
    have hEPart : E.part (x i) = E.part (x j) :=
      D.transversal R (E.part ∘ x) hDRel i j hSame
    exact E.transversal R x hx i j hEPart

/-- Coarsening through an already partite base preserves the required
homomorphism-embedding projection invariant. -/
theorem System.coarsenVia_isPartiteOver
    (D : System L Q P) (E : System L P X)
    (A : RelStructure L Q)
    (hE : E.IsPartiteOver D.toRelStructure)
    (hD : D.IsPartiteOver A) :
    (E.coarsenVia D hE).IsPartiteOver A := by
  change E.toRelStructure.IsHomomorphismEmbedding A (D.part ∘ E.part)
  exact hD.comp hE

/-- A genuinely P-partite embedding remains Q-partite after BOTH
source and destination are coarsened through the same base D. -/
def Embedding.coarsenVia
    (D : System L Q P)
    (B : System L P X) (E : System L P Y)
    (hB : B.IsPartiteOver D.toRelStructure)
    (hE : E.IsPartiteOver D.toRelStructure)
    (f : Embedding B E) :
    Embedding (B.coarsenVia D hB) (E.coarsenVia D hE) where
  toEmbedding := f.toEmbedding
  map_part x := congrArg D.part (f.map_part x)

end StructuralRamsey.Partite

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {P Q VB X : Type v}

/-- A selected relational target copy over a LARGE base D is an
actual Q-partite gluing copy after coarsening, provided its prescribed
base embedding respects the original Q-partition of the target.
The underlying embedding and ALL selected labels remain unchanged. -/
def DesignatedCopy.toCoarsenedPartiteEmbedding
    (Target : StructuralRamsey.Partite.System L Q VB)
    (D : StructuralRamsey.Partite.System L Q P)
    (E : StructuralRamsey.Partite.System L P X)
    (hE : E.IsPartiteOver D.toRelStructure)
    (family : Set (RelStructure.Embedding Target.toRelStructure D.toRelStructure))
    (q : DesignatedCopy Target.toRelStructure D.toRelStructure E family)
    (hPart : ∀ x : VB, D.part (q.base x) = Target.part x) :
    StructuralRamsey.Partite.Embedding
      Target (E.coarsenVia D hE) where
  toEmbedding := q.embedding
  map_part x := (congrArg D.part (q.projects x)).trans (hPart x)

/-- The ENTIRE actual selected label subtype becomes a bona fide Q-partite
gluing family, without quotienting labels or deleting ambient edges.
No injective map from the whole target to Q is required. -/
def selectedPartiteGluingFamily_of_largeBase
    (Target : StructuralRamsey.Partite.System L Q VB)
    (D : StructuralRamsey.Partite.System L Q P)
    (E : StructuralRamsey.Partite.System L P X)
    (hE : E.IsPartiteOver D.toRelStructure)
    (family : Set (RelStructure.Embedding Target.toRelStructure D.toRelStructure))
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      D.part (b x) = Target.part x)
    (selected : Set (DesignatedCopy Target.toRelStructure D.toRelStructure E family)) :
    {q : DesignatedCopy Target.toRelStructure D.toRelStructure E family //
      q ∈ selected} →
      StructuralRamsey.Partite.Embedding Target (E.coarsenVia D hE) :=
  fun q => q.1.toCoarsenedPartiteEmbedding Target D E hE family
    (hFamilyParts q.1.base q.1.base_mem)

end StructuralRamsey.Girth
