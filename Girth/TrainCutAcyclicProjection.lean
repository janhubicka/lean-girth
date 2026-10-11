import Girth.IncidenceCompression

/-!
# Berge-cycle projection to an acyclic labelled wagon cut

Partition a physical edge family by arbitrary edge-class labels. If
a Berge cycle changes labels, each genuine label transition gives a
connector vertex in both labelled wagon carriers. The verified raw
cyclic-incidence compression builds an incidence circuit of these
carriers. Thus a labelled carrier cut whose incidence graph is
acyclic forces every Berge cycle to stay inside a single class.

This gives the exact acyclic-cut / cycle-projection interface.
It does NOT yet convert finite cut girth >g into a quantitative
lower bound for original cycles; the first-wagon refinement count
and projected child-cycle girth arguments remain separate.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- Carrier of one edge-partition class, retaining its label even if
two distinct classes have the same physical vertex carrier. -/
def edgePartitionClassCarrier
    (H : Set (Set W)) (part : Set W → I) (i : I) : Set W :=
  {x | ∃ e : Set W, e ∈ H ∧ part e = i ∧ x ∈ e}

/-- With an acyclic labelled wagon-carrier incidence graph, every
Berge cycle in H has a CONSTANT edge-partition label. -/
theorem bergeCycle_partition_constant_of_acyclic_cut
    {H : Set (Set W)}
    (part : Set W → I)
    (hAcyclic :
      (boundaryIncidenceGraph (edgePartitionClassCarrier H part)).IsAcyclic)
    (c : BergeCycle H) :
    ∀ i j : Fin c.length,
      part (c.edge i) = part (c.edge j) := by
  by_contra h
  push_neg at h
  obtain ⟨i, j, hij⟩ := h
  let owner : Fin c.length → I := fun k => part (c.edge k)
  have hBoundary :
      ∀ k, owner k ≠ owner (cyclicSucc k) →
        c.vertex k ∈ edgePartitionClassCarrier H part (owner k) ∧
        c.vertex k ∈
          edgePartitionClassCarrier H part (owner (cyclicSucc k)) := by
    intro k _
    constructor
    · exact ⟨c.edge k, c.edge_mem k, rfl, c.left_mem k⟩
    · exact ⟨c.edge (cyclicSucc k), c.edge_mem (cyclicSucc k),
        rfl, c.right_mem k⟩
  obtain ⟨d, _⟩ :=
    RawCyclicIncidenceData.exists_compressed_ofBergeCycle
      c owner (edgePartitionClassCarrier H part) hBoundary ⟨i, j, hij⟩
  exact CyclicIncidenceData.no_cyclicIncidenceData_of_acyclic hAcyclic d

end StructuralRamsey.Girth
