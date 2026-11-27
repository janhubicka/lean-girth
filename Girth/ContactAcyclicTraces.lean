import Girth.ContactEdgeTraces
import Girth.ContactEraseNode
import Girth.ContactBoostClass
import Girth.IncidenceCircuit

/-! The general acyclic-incidence versions of the trace-tree and node-erasure
lemmas. The edge labels can be the distinct edge sets themselves; repetitions
of a trace remain separate labels in the resulting join tree. -/

namespace StructuralRamsey.Girth
universe v
variable {V E J I : Type v}

/-- An acyclic incidence graph rules out labelled Berge cycles of every size. -/
theorem contact_labelledGirth_of_incidence_acyclic
    (edge : E → Set V) (h : (boundaryIncidenceGraph edge).IsAcyclic) (q : ℕ) :
    LabelledGirthGT edge q := by
  rintro ⟨C,_⟩
  let d : CyclicIncidenceData edge := {
    length := C.length
    hlength := C.hlength
    label := C.label
    connector := C.vertex
    connector_injective := C.vertex_injective
    label_ne_succ := fun i he =>
      contactSucc_ne C.hlength i (C.label_injective he).symm
    left_mem := C.left_mem
    right_mem := C.right_mem }
  exact CyclicIncidenceData.no_cyclicIncidenceData_of_acyclic h d

/-- A finite family of empty, singleton and edge traces of an incidence forest
has a join tree, with no cardinality cutoff in the hypotheses. -/
theorem contact_trace_joinTree_of_incidence_acyclic
    [Fintype V] [Fintype J] [Nonempty J]
    (edge : E → Set V) (F : J → Set V)
    (ht : ContactEdgeTraces edge F)
    (h : (boundaryIncidenceGraph edge).IsAcyclic) :
    Nonempty (ContactJoinTree F) := by
  have hg := contact_labelledGirth_of_incidence_acyclic edge h
  have hlin := contact_pairwise_of_labelledGirth edge (q := 2) (by omega) (hg 2)
  exact contact_trace_joinTree edge F ht hlin (le_refl (Fintype.card J))
    (hg (Fintype.card J))

/-- The general incidence-forest input supplies the neighbour trace tree used
by the checked node erasure construction. A node with no neighbour is the
separate empty-family case of the forest convention. -/
theorem ContactJoinTree.erase_of_incidence_acyclic
    [Fintype V] [Fintype I] {F : I → Set V}
    (T : ContactJoinTree F) (center : I)
    [Nonempty (T.tree.neighborSet center)]
    (edge : E → Set V)
    (ht : ContactEdgeTraces edge (T.neighborTraces center))
    (h : (boundaryIncidenceGraph edge).IsAcyclic) :
    Nonempty (ContactJoinTree (contactEraseSet F center)) := by
  classical
  letI : Fintype (T.tree.neighborSet center) := Fintype.ofFinite _
  obtain ⟨R⟩ := contact_trace_joinTree_of_incidence_acyclic edge
    (T.neighborTraces center) ht h
  exact ⟨T.eraseWithTraces center R⟩

end StructuralRamsey.Girth
