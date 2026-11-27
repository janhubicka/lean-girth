import Girth.ContactExpansionConstruction

/-! The positive-core preservation theorem, at one actual generated
partition level. The input is the compatible gluing on a strongly
induced active strip, not an assumed output geometry or cycle bound.
The mixed-forest core alternative at level zero is separate. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P V₀ E₀ I₀ P₀ : Type v}

namespace ContactTaggedPicture
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    (T : ContactTaggedPicture D L)

theorem preserves_systemGirth_positive {q : ℕ} (hq : 2 ≤ q)
    (hstrip : T.StripStrong) (hD : D.ContactSystemGirthGT q)
    (hL : L.ContactSystemGirthGT q) : T.output.ContactSystemGirthGT q := by
  let A := T.toPictureData
  have hD2 := D.contactSystemGirthGT_mono hD hq
  have hc : A.CoreStrong := T.core_strong hstrip
  have hs : A.StandardStrong := A.standard_strong hc hD.g1
  have hlin : T.output.ContactLinear :=
    ⟨A.edge_linearity hc hs hD.linear hL.linear,
      A.wagon_linearity hD.linear hD.g1 hD.g2 hD2.g4 hL.linear⟩
  have htwo := A.meets_of_two_vertices hD.g1 hD.g2 hD2.g4 hL.linear
  have h1 := T.pictureCopies.preserves_g1 hD.g1 hD.g2 hL.g1 hs htwo
  have h2 := T.pictureCopies.preserves_g2 hD.g2 hL.g2
  have h4 := T.pictureCopies.preserves_g4_positive hD.linear hD.g1 hD.g2 htwo hD.g4 hL.g4
  exact ⟨hlin,h1,h2,T.pictureCopies.preserves_g3_of_g4
    hD.g1 hD.g2 h1 h2 hlin h4 hL.g3,h4⟩

end ContactTaggedPicture
end StructuralRamsey.Girth
