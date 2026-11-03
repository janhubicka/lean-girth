import Girth.Support
import PartiteConstruction.Partite.Induced

set_option autoImplicit false

/-!
# Full A-support coverage in an induced partite Ramsey power

The large-base Hales--Jewett construction must retain a copy of A
through EVERY physical vertex. This cannot be inferred from a mere
homomorphism of the part map.

A family of A-embeddings e_i:A->B, one for each coordinate, which
preserve the Q-parts, defines one genuine A-embedding into the
induced power: at part q use the tuple (e_i(q))_i. Its image is
induced, because the power relations are coordinatewise and N>0.

If B's vertices are all covered by genuine A-copies and EVERY
relational A-copy in B is Q-part-preserving (the finite ordered
rigidity result in Track D #785), take for each coordinate i an
A-copy through x.coord(i). Part preservation ensures it hits that
vertex exactly at the part x.part. Combining the coordinate copies
produces an A-copy of the power passing through x itself.

No source edge is deleted; every vertex of the complete partite
power is covered. This is another actual initial-stage requirement
for the proposed large Ramsey base, independent of A-linearity
(#787), system-girth and attached-output supreme cycles.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {Q V : Type v}
variable (A : RelStructure L Q)
variable (B : StructuralRamsey.Partite.System L Q V)
variable (N : ℕ) (hN : 0 < N)

local notation "Power" => StructuralRamsey.Partite.Induced.power B N

/-- Given true part-preserving A-copies at EVERY coordinate, combine
them into a full relational A-embedding of the entire induced power.
The positive exponent is used for relation REFLECTION. -/
def inducedPower_embedding_of_coordinateCopies
    (copies : Fin N → Embedding A B.toRelStructure)
    (hParts : ∀ i : Fin N, ∀ x : Q, B.part (copies i x) = x) :
    Embedding A (Power).toRelStructure where
  toFun := fun x => {
    part := x
    coord := fun i => copies i x
    belongs := fun i => hParts i x
  }
  injective := by
    intro x y hxy
    exact congrArg
      (fun z : StructuralRamsey.Partite.NonInduced.Vertex B N => z.part) hxy
  map_rel_iff := by
    intro R z
    constructor
    · intro hPower
      let i0 : Fin N := ⟨0, hN⟩
      exact ((copies i0).map_rel_iff R z).mp (hPower i0)
    · intro hA i
      exact ((copies i).map_rel_iff R z).mpr hA

/-- Each coordinate of the combined embedding is its prescribed
original A-copy, without a quotient or carrier-level identification. -/
theorem inducedPower_embedding_of_coordinateCopies_coord
    (copies : Fin N → Embedding A B.toRelStructure)
    (hParts : ∀ i : Fin N, ∀ x : Q, B.part (copies i x) = x)
    (x : Q) (i : Fin N) :
    ((inducedPower_embedding_of_coordinateCopies A B N hN copies hParts) x).coord i =
      copies i x := rfl

/-- Every actual power vertex belongs to the physical carrier of an
A-copy, provided the original target has full A-support coverage and
its A-copies preserve the Q-part map. The conclusion concerns ALL
power vertices, not only the selected HJ lines. -/
theorem inducedPower_supportCovers_of_partiteACopies
    (hCover : ∀ x : V, ∃ a : Embedding A B.toRelStructure,
      x ∈ copyCarrier a)
    (hPart : ∀ a : Embedding A B.toRelStructure, ∀ q : Q,
      B.part (a q) = q) :
    ∀ x : StructuralRamsey.Partite.NonInduced.Vertex B N,
      ∃ a : Embedding A (Power).toRelStructure,
        x ∈ copyCarrier a := by
  classical
  intro x
  have hCopies (i : Fin N) :
      ∃ a : Embedding A B.toRelStructure, a x.part = x.coord i := by
    obtain ⟨a, ⟨q, hq⟩⟩ := hCover (x.coord i)
    have hPartEq : q = x.part := by
      calc
        q = B.part (a q) := (hPart a q).symm
        _ = B.part (x.coord i) := congrArg B.part hq
        _ = x.part := x.belongs i
    subst q
    exact ⟨a, hq⟩
  let copies (i : Fin N) : Embedding A B.toRelStructure :=
    Classical.choose (hCopies i)
  have hAt (i : Fin N) : copies i x.part = x.coord i :=
    Classical.choose_spec (hCopies i)
  let e := inducedPower_embedding_of_coordinateCopies
    A B N hN copies (fun i q => hPart (copies i) q)
  refine ⟨e, ⟨x.part, ?_⟩⟩
  apply StructuralRamsey.Partite.NonInduced.Vertex.ext B
  · rfl
  · intro i
    exact hAt i

end StructuralRamsey.Girth
