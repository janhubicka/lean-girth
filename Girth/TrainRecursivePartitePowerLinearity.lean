import Girth.Support
import PartiteConstruction.Partite.Induced

set_option autoImplicit false

/-!
# A-linearity of the genuine induced partite Hales--Jewett power

The large-base Hales--Jewett construction in Track D needs the base
to be A-linear, not merely partite over A.

A relational A-embedding into an induced power which preserves its
A-part projection gives a genuine relational A-embedding into the
original target at EACH Hales--Jewett coordinate.  Relation
preservation is coordinatewise; reflection follows from the
original target's projection homomorphism to A and the exact part
labels.  No new edges are postulated.

Assume the target B is A-linear.  If two distinct A-copies in the
power share two physical vertices, they share the same two A-part
coordinates. At every HJ coordinate, their projections are A-copies
of B sharing two distinct vertices, so A-linearity forces their
carriers equal. Since both coordinate maps preserve the parts and
a copy has exactly one vertex in each source part, the two projected
embeddings agree pointwise at that coordinate. Thus the original
power embeddings coincide, a contradiction.

The only extra hypothesis is that ALL relational A-embeddings of the
power preserve A-parts. For finite ordered irreducible A this follows
from Track D's rigid-source lemma (#785) and the checked fact that
positive powers remain partite over A. The ordered specialization is
left separate until that source lemma is merged. No appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {Q V : Type v}
variable (A : RelStructure L Q)
variable (B : StructuralRamsey.Partite.System L Q V)
variable (hB : B.IsPartiteOver A)
variable (N : ℕ)

local notation "Power" => StructuralRamsey.Partite.Induced.power B N

/-- Coordinate evaluation of a genuinely part-preserving A-copy in a
power is a full relational embedding in the original A-partite B.
In particular it reflects all relations, not merely preserves them. -/
def inducedPower_coordinateAEmbedding
    (e : Embedding A (Power).toRelStructure)
    (hPart : ∀ x : Q, (Power).part (e x) = x)
    (i : Fin N) : Embedding A B.toRelStructure where
  toFun x := (e x).coord i
  injective := by
    intro x y hxy
    calc
      x = (Power).part (e x) := (hPart x).symm
      _ = B.part ((e x).coord i) := ((e x).belongs i).symm
      _ = B.part ((e y).coord i) := congrArg B.part hxy
      _ = (Power).part (e y) := (e y).belongs i
      _ = y := hPart y
  map_rel_iff := by
    intro R z
    constructor
    · intro hRel
      have hA : A.rel R (fun j => B.part ((e (z j)).coord i)) :=
        hB.1 R (fun j => (e (z j)).coord i) hRel
      have hEq : (fun j => B.part ((e (z j)).coord i)) = z := by
        funext j
        exact ((e (z j)).belongs i).trans (hPart (z j))
      rw [hEq] at hA
      exact hA
    · intro hA
      have hPower : (Power).rel R (e ∘ z) :=
        (e.map_rel_iff R z).mpr hA
      exact hPower i

/-- The coordinate embedding has the ORIGINAL A-part map exactly,
even though the power's vertex carrier may have many vertices in
each part. -/
theorem inducedPower_coordinateAEmbedding_parts
    (e : Embedding A (Power).toRelStructure)
    (hPart : ∀ x : Q, (Power).part (e x) = x)
    (i : Fin N) (x : Q) :
    B.part (inducedPower_coordinateAEmbedding A B hB N e hPart i x) = x :=
  ((e x).belongs i).trans (hPart x)

include hB

/-- Genuine A-linearity persists under the positive-or-zero induced
partite power as soon as its A-embeddings are actual A-part-preserving
copies. The proof keeps complete physical carriers and treats distinct
edge labels by actual carrier equality rather than quotienting labels. -/
theorem aLinear_inducedPower_of_Aparts
    (hLinear : ALinear A B.toRelStructure)
    (hPowerPart : ∀ e : Embedding A (Power).toRelStructure,
      ∀ x : Q, (Power).part (e x) = x) :
    ALinear A (Power).toRelStructure := by
  intro e f hNotSame x hx y hy
  by_contra hxy
  obtain ⟨u, hu⟩ := hx.1
  obtain ⟨u', hu'⟩ := hx.2
  obtain ⟨v, hv⟩ := hy.1
  obtain ⟨v', hv'⟩ := hy.2
  have huu' : u = u' := by
    calc
      u = (Power).part (e u) := (hPowerPart e u).symm
      _ = (Power).part (f u') := congrArg (Power).part (hu.trans hu'.symm)
      _ = u' := hPowerPart f u'
  have hvv' : v = v' := by
    calc
      v = (Power).part (e v) := (hPowerPart e v).symm
      _ = (Power).part (f v') := congrArg (Power).part (hv.trans hv'.symm)
      _ = v' := hPowerPart f v'
  subst u'
  subst v'
  have heu : e u = f u := hu.trans hu'.symm
  have hev : e v = f v := hv.trans hv'.symm
  have huv : u ≠ v := by
    intro heq
    apply hxy
    calc
      x = e u := hu.symm
      _ = e v := congrArg e heq
      _ = y := hv
  have hCoords : ∀ i : Fin N, ∀ w : Q,
      (e w).coord i = (f w).coord i := by
    intro i
    let eI := inducedPower_coordinateAEmbedding A B hB N e (hPowerPart e) i
    let fI := inducedPower_coordinateAEmbedding A B hB N f (hPowerPart f) i
    have hAtU : eI u = fI u := congrArg (fun z => z.coord i) heu
    have hAtV : eI v = fI v := congrArg (fun z => z.coord i) hev
    have hCarrier : SameCopy eI fI := by
      by_contra hNo
      have hSmall := hLinear eI fI hNo
      have hU : eI u ∈ copyCarrier eI ∩ copyCarrier fI :=
        ⟨⟨u, rfl⟩, ⟨u, hAtU.symm⟩⟩
      have hV : eI v ∈ copyCarrier eI ∩ copyCarrier fI :=
        ⟨⟨v, rfl⟩, ⟨v, hAtV.symm⟩⟩
      exact huv (eI.injective (hSmall hU hV))
    intro w
    have hMember : eI w ∈ copyCarrier fI := by
      rw [← hCarrier]
      exact ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := hMember
    have hwz : w = z := by
      calc
        w = B.part (eI w) :=
          (inducedPower_coordinateAEmbedding_parts A B hB N e
            (hPowerPart e) i w).symm
        _ = B.part (fI z) := congrArg B.part hz.symm
        _ = z :=
          inducedPower_coordinateAEmbedding_parts A B hB N f
            (hPowerPart f) i z
    subst z
    exact hz.symm
  have hEmb : e = f := by
    apply Embedding.ext
    intro w
    apply StructuralRamsey.Partite.NonInduced.Vertex.ext B
    · exact (hPowerPart e w).trans (hPowerPart f w).symm
    · intro i
      exact hCoords i w
  exact hNotSame (by rw [hEmb]; rfl)

end StructuralRamsey.Girth
