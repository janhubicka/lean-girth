import Girth.TrainCutAcyclicProjection
import Girth.ForestCompletionOwnerImage
import Girth.BoundaryIncidenceAcyclic

/-!
# Quantitative projection of a short Berge cycle to a labelled wagon cut

If a cycle changes the equivalence-class label of its physical edges,
the owner-change connectors form a cyclic incidence trail in the
LABELLED carrier cut. Restrict this cut to the finite image of the
labels used by the cycle: at most its length, hence at most g.
Under labelled carrier linearity and cut Berge girth >g, the
restricted incidence graph is acyclic, contradicting the checked
cyclic-run compression theorem.

Unlike a qualitative acyclic-cut statement, this handles a full
finite girth bound: every physical Berge cycle of length <=g stays
inside a single class. No assumptions on the total number of cut
wagons are needed, and distinct labels remain distinct even if
their carriers coincide.

The theorem does not yet construct generated train ancestor labels
or prove tail acceptable-cycle system-Girth.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- At cut girth greater than g, a physical Berge cycle of length
at most g cannot use two different cut-equivalence labels. -/
theorem bergeCycle_partition_constant_of_cut_girth
    {H : Set (Set W)}
    (part : Set W → I)
    (g : ℕ)
    (hLabelLinear :
      ∀ ⦃i j : I⦄, i ≠ j →
        (edgePartitionClassCarrier H part i ∩
          edgePartitionClassCarrier H part j).Subsingleton)
    (hCutGirth :
      GirthGT (Set.range (edgePartitionClassCarrier H part)) g)
    (c : BergeCycle H)
    (hShort : c.length ≤ g) :
    ∀ i j : Fin c.length,
      part (c.edge i) = part (c.edge j) := by
  classical
  by_contra hConstant
  push Not at hConstant
  obtain ⟨i, j, hij⟩ := hConstant
  let raw : Fin c.length → I := fun k => part (c.edge k)
  letI : Fintype (OwnerImage raw) := by
    exact OwnerImage.fintype raw
  let carrier : OwnerImage raw → Set W :=
    fun t => edgePartitionClassCarrier H part t.val
  have hCard : Fintype.card (OwnerImage raw) ≤ g := by
    have hn : Fintype.card (Fin c.length) ≤ g := by
      simpa using hShort
    exact (OwnerImage.card_le raw).trans hn
  have hCarrierLinear :
      ∀ ⦃a b : OwnerImage raw⦄, a ≠ b →
        (carrier a ∩ carrier b).Subsingleton := by
    intro a b hab
    have hne : a.val ≠ b.val := by
      intro heq
      exact hab (Subtype.ext heq)
    exact hLabelLinear hne
  have hRange :
      Set.range carrier ⊆
        Set.range (edgePartitionClassCarrier H part) := by
    rintro t ⟨a, rfl⟩
    exact ⟨a.val, rfl⟩
  have hRestrictedGirth : GirthGT (Set.range carrier) g :=
    girthGT_of_subset hRange hCutGirth
  have hAcyclic : (boundaryIncidenceGraph carrier).IsAcyclic :=
    boundaryIncidenceGraph_isAcyclic_of_pairwiseSubsingleton_of_girthGT
      carrier hCarrierLinear g hCard hRestrictedGirth
  let picked : Fin c.length → OwnerImage raw :=
    OwnerImage.owner raw
  have hBoundary :
      ∀ k, picked k ≠ picked (cyclicSucc k) →
        c.vertex k ∈ carrier (picked k) ∧
        c.vertex k ∈ carrier (picked (cyclicSucc k)) := by
    intro k _
    constructor
    · exact ⟨c.edge k, c.edge_mem k, rfl, c.left_mem k⟩
    · exact ⟨c.edge (cyclicSucc k),
        c.edge_mem (cyclicSucc k), rfl, c.right_mem k⟩
  have hNonconstant :
      ∃ i j : Fin c.length, picked i ≠ picked j := by
    refine ⟨i, j, ?_⟩
    intro heq
    exact hij (congrArg Subtype.val heq)
  obtain ⟨d, _⟩ :=
    RawCyclicIncidenceData.exists_compressed_ofBergeCycle
      c picked carrier hBoundary hNonconstant
  exact CyclicIncidenceData.no_cyclicIncidenceData_of_acyclic hAcyclic d

end StructuralRamsey.Girth
