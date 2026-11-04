import Girth.TrainRecursivePartitePowerLinearity

set_option autoImplicit false
set_option Elab.async false

/-!
# Two-point rigidity of A-copy coordinates in an induced partite power

For a genuinely A-part-preserving embedding, its values at two
distinct A-parts determine its entire image copy inside an A-linear
target, *provided we compare two A-embeddings*. Indeed two common
vertices contradict A-linearity unless the two copies have the same
carrier; the part map then identifies their parametrizations exactly.

As an immediate application, if two coordinate projections of an
A-copy in an induced partite power agree at two different source
parts, they agree at every part. This is the variable-coordinate
rigidity needed to prove that Hales--Jewett line embeddings have
A-strong range under the appropriate source conditions.

The present module proves only this true rigidity kernel, not the
whole line-image A-strongness claim. It makes no quotient of
distinct support labels, uses no added axioms, and changes no
circulation manuscript text.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {Q V : Type v}

/-- In an A-linear partite target, two genuine part-preserving
A-embeddings which agree on two DISTINCT source parts agree
everywhere. Both the carrier equality and its unique part
parametrization are established, not assumed. -/
theorem aLinear_partPreserving_twoPoint_eq
    (A : RelStructure L Q)
    (B : StructuralRamsey.Partite.System L Q V)
    (hLinear : ALinear A B.toRelStructure)
    (e f : Embedding A B.toRelStructure)
    (hE : ∀ x : Q, B.part (e x) = x)
    (hF : ∀ x : Q, B.part (f x) = x)
    (u v : Q) (huv : u ≠ v)
    (hu : e u = f u) (hv : e v = f v) :
    e = f := by
  classical
  have hCarrier : SameCopy e f := by
    by_contra hNot
    have hSmall := hLinear e f hNot
    have hU : e u ∈ copyCarrier e ∩ copyCarrier f :=
      ⟨⟨u, rfl⟩, ⟨u, hu.symm⟩⟩
    have hV : e v ∈ copyCarrier e ∩ copyCarrier f :=
      ⟨⟨v, rfl⟩, ⟨v, hv.symm⟩⟩
    exact huv (e.injective (hSmall hU hV))
  apply Embedding.ext
  intro w
  have hw : e w ∈ copyCarrier f := by
    rw [← hCarrier]
    exact ⟨w, rfl⟩
  obtain ⟨z, hz⟩ := hw
  have hwz : w = z := by
    calc
      w = B.part (e w) := (hE w).symm
      _ = B.part (f z) := congrArg B.part hz.symm
      _ = z := hF z
  subst z
  exact hz.symm

/-- Two coordinate embeddings of the SAME actual A-copy in an
induced power are identical if they agree at two distinct A-parts.
The coordinate maps are proved to be genuine *relational*
A-embeddings and preserve part labels by the existing checked
induced-power API. -/
theorem inducedPower_twoCoordinate_agreement
    (A : RelStructure L Q)
    (B : StructuralRamsey.Partite.System L Q V)
    (hB : B.IsPartiteOver A)
    (hLinear : ALinear A B.toRelStructure)
    (N : ℕ)
    (e : Embedding A
      (StructuralRamsey.Partite.Induced.power B N).toRelStructure)
    (hParts : ∀ x : Q,
      (StructuralRamsey.Partite.Induced.power B N).part (e x) = x)
    (i j : Fin N) (u v : Q) (huv : u ≠ v)
    (hu : (e u).coord i = (e u).coord j)
    (hv : (e v).coord i = (e v).coord j) :
    ∀ w : Q, (e w).coord i = (e w).coord j := by
  let eI := inducedPower_coordinateAEmbedding A B hB N e hParts i
  let eJ := inducedPower_coordinateAEmbedding A B hB N e hParts j
  have hEq : eI = eJ :=
    aLinear_partPreserving_twoPoint_eq A B hLinear eI eJ
      (inducedPower_coordinateAEmbedding_parts A B hB N e hParts i)
      (inducedPower_coordinateAEmbedding_parts A B hB N e hParts j)
      u v huv hu hv
  intro w
  exact congrArg (fun a : Embedding A B.toRelStructure => a w) hEq

end StructuralRamsey.Girth
