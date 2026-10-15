import Girth.TrainSimultaneousSupreme
import Girth.TrainInteriorParentQuotientBridge

/-!
# Circulation: a supreme copy contains every vertex connector

This property is used in the general two-standard obstruction and
in lifting a supreme reduced cycle. It does NOT follow from the bare
abstract incidence record unless source edges actually lie in the
vertex carrier of their designated copy. State that elementary
compatibility explicitly rather than smuggling it into the data.

With compatibility, the proof is short: if the label incident with
a given vertex connector is the retained supreme label, membership
is immediate; otherwise its chosen short or long piece uses an edge
belonging to that supreme copy and incident with the vertex.

The genuine shared-witness `OrderOneData` satisfies compatibility
definitionally, because its copy carrier is the union of the
physical edge carriers in the genuine shared-to-core edge range.
Only circulation, no appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Genuine designated-copy edges must carry only vertices of that
copy. This is not part of the minimal four-field OrderOneData record. -/
def CopyEdgeCarrierCompatible : Prop :=
  ∀ (i : I) (e : E), e ∈ D.copyEdges i →
    D.edgeCarrier e ⊆ D.copyCarrier i

/-- Every vertex connector of a genuinely simultaneous supreme cycle
belongs to the vertex carrier of the designated supreme copy.

The output names its actual retained index AND designated copy index;
it does not merely report that some unspecified copy covers vertices.
No acceptability or girth hypothesis is needed after a valid
simultaneous supreme plan has been supplied. -/
theorem BigCycle.supreme_copy_contains_vertex_connectors
    {n : ℕ} (C : D.BigCycle n)
    (hCompat : D.CopyEdgeCarrierCompatible)
    (hSup : C.HasSimultaneousSupreme) :
    ∃ (k : Fin n) (i : I),
      C.label k = Sum.inl i ∧
      ∀ (j : Fin n) (x : V),
        C.connector j = Sum.inl x → x ∈ D.copyCarrier i := by
  obtain ⟨k, hk, hPieces⟩ :=
    BigCycle.localSupreme_of_simultaneous D C hSup
  cases hLabel : C.label k with
  | inl i =>
      refine ⟨k, i, hLabel, ?_⟩
      intro j x hx
      by_cases hEq : C.label j = C.label k
      · have hInc := C.left_incident j
        rw [hEq, hLabel, hx] at hInc
        simpa [Incident, carrier] using hInc
      · have hp := hPieces j hEq
        rcases hp with ⟨e, he, _hPrev, hCurrent⟩ |
            ⟨u, w, p, e, f, _hPrev, hCurrent, he, hf,
              _hef, _hep, _hfp, _hue, hwf, _hNoEdge⟩
        · have hSource : e ∈ D.copyEdges i := by
            simpa [edges, hLabel] using he
          have hVertex : x ∈ D.edgeCarrier e := by
            simpa [Incident, carrier, hx] using hCurrent
          exact hCompat i e hSource hVertex
        · have hwx : w = x := by
            exact Sum.inl.inj (hCurrent.symm.trans hx)
          have hSource : f ∈ D.copyEdges i := by
            simpa [edges, hLabel] using hf
          exact hCompat i f hSource (by simpa [hwx] using hwf)
  | inr e =>
      simp [designated, hLabel] at hk

end StructuralRamsey.Girth.OrderOneData

namespace StructuralRamsey.Girth

universe v
variable {W CoreEdge Shared I : Type v}

/-- The actual shared-witness incidence record is automatically
compatible: every source edge of label i occurs as the core image
of a genuinely shared edge, hence its full vertex carrier is
contained in the chosen union defining copyCarrier i. -/
theorem sharedWitnessOrderOneData_copyEdgeCarrierCompatible
    {m : ℕ} (T : EdgeTrainLevels CoreEdge m)
    (μ : Fin (m + 1))
    (embed : I → Shared ↪ CoreEdge)
    (carrier : CoreEdge → Set W) :
    (sharedWitnessOrderOneData T μ embed carrier).CopyEdgeCarrierCompatible := by
  intro i e he x hx
  change e ∈ Set.range (embed i) at he
  obtain ⟨s, hs⟩ := he
  change x ∈ carrier e at hx
  exact ⟨s, by simpa only [hs] using hx⟩

end StructuralRamsey.Girth
