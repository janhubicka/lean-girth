import Girth.TrainWagonPairUniqueness
import Girth.TrainTwoCopyLocalSymmetry

/-!
# Circulation: the unique witness wagon for both two-copy long pieces

Two distinct designated copies sharing distinct vertices x,y admit
local short or long pieces under the genuine order-two system bound.
If no ambient edge contains the pair, short pieces are impossible,
and both copies supply long pieces. In a linear pretrain the parent
wagon of those four physical source edges is necessarily the SAME.

The output states the genuine two-edge incidence in both copies, not
merely abstract wagon membership or a local-supreme label. It is the
intrinsic witness-side half of the edge-block two-standard argument.

The full generated picture-step quotient transport, general cycle
transfer, and appendix are not part of this lemma.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- If two designated copies share two different vertices x,y but
there is no ambient edge through both, their source long pieces are
forced to use one and the same actual wagon. -/
theorem twoVertexTwoCopyCycle_common_long_wagon
    (hLinear : D.LinearPretrain)
    (hBound : D.LocalPieceSystemBound 2)
    (i j : I) (x y : V) (hij : i ≠ j) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j)
    (hNoEdge : ¬ D.PairEdge x y) :
    ∃ w : P,
      (∃ e f : E,
        e ∈ D.edges (.inl i) ∧ f ∈ D.edges (.inl i) ∧
        e ≠ f ∧ D.parent e = w ∧ D.parent f = w ∧
        x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier f) ∧
      (∃ e f : E,
        e ∈ D.edges (.inl j) ∧ f ∈ D.edges (.inl j) ∧
        e ≠ f ∧ D.parent e = w ∧ D.parent f = w ∧
        x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier f) := by
  obtain ⟨hPieceI, hPieceJ⟩ :=
    D.twoVertexTwoCopyCycle_both_local_pieces hBound
      i j x y hij hxy hix hiy hjx hjy
  have hNoShort (a : I ⊕ E) :
      ¬ D.ShortPiece a (.inl x) (.inl y) := by
    rintro ⟨e, _he, hxe, hye⟩
    exact hNoEdge ⟨e,
      (by simpa [Incident, carrier] using hxe),
      (by simpa [Incident, carrier] using hye)⟩
  have hLongI : D.LongPiece (.inl i) (.inl x) (.inl y) :=
    hPieceI.resolve_left (hNoShort (.inl i))
  have hLongJ : D.LongPiece (.inl j) (.inl x) (.inl y) :=
    hPieceJ.resolve_left (hNoShort (.inl j))
  obtain ⟨u, v, w, a, b, hu, hv, ha, hb, hab,
    haw, hbw, hxa, hyb, _hNoPair⟩ := hLongI
  have hux : u = x := (Sum.inl.inj hu).symm
  have hvy : v = y := (Sum.inl.inj hv).symm
  subst u
  subst v
  obtain ⟨c, d, hc, hd, hcd, hcw, hdw, hxc, hyd, _⟩ :=
    D.longPiece_edges_in_given_wagon hLinear
      (.inl j) w x y
      ⟨a, haw, hxa⟩ ⟨b, hbw, hyb⟩ hxy hLongJ
  exact ⟨w,
    ⟨a, b, ha, hb, hab, haw, hbw, hxa, hyb⟩,
    ⟨c, d, hc, hd, hcd, hcw, hdw, hxc, hyd⟩⟩

end StructuralRamsey.Girth.OrderOneData
