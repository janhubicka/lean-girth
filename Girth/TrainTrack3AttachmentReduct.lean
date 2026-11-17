import PartiteConstruction.Partite.Attachment

set_option autoImplicit false

namespace StructuralRamsey.Girth

universe u v

variable {L : RelLanguage.{u}} {P X Y I : Type v}

/-- Partite restriction has the same relational reduct as restriction
of the underlying structure. -/
theorem track3_partiteInduce_toRelStructure_eq
    (C : Partite.System L P X) (S : Set X) :
    (C.induce S).toRelStructure = C.toRelStructure.induce S := rfl

/-- Free partite attachment uses exactly the relational attachment of the
underlying structures along the given embeddings. -/
theorem track3_partiteAttachment_toRelStructure_eq
    (C : Partite.System L P X) (S : Set X)
    (R : Partite.System L P Y)
    (f : I → Partite.Embedding (C.induce S) R) :
    (Partite.Attachment.attach C S R f).toRelStructure =
      RelStructure.Attachment.attach C.toRelStructure S R.toRelStructure
        (fun i => (f i).toEmbedding) := rfl

end StructuralRamsey.Girth
