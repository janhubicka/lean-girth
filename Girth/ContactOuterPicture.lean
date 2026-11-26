import Girth.ContactTrainPicture
import Girth.ContactMarkedEdges
import Girth.ContactQualitativeCompletion

/-! The outer partite picture uses exactly the same actual
gluing as the train induction, at height one. Instead of the
bottom system condition, maintain qualitative completion of
small designated families, global allowed intersections, and
coverage by the designated copies. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B : Type v}

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)

def CopyCovered : Prop :=
  (∀ x, ∃ i, x ∈ D.copyCarrier i) ∧ (∀ e, ∃ i, e ∈ D.copyEdges i)

end ContactHypergraphData

namespace ContactBaseProjection
variable {D : ContactHypergraphData V E I} {base : B → Set X}
    (P : ContactBaseProjection D base)

/-- Transversality gives at most one edge over a specified base
edge in each designated copy. Label equality follows from linearity
and two distinct vertices of the base edge. -/
theorem marked_edge_unique (b : B) (hsize : (base b).Nontrivial)
    (hlin : ∀ e f, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (i : I) (e f : E) (he : e ∈ D.copyEdges i) (hf : f ∈ D.copyEdges i)
    (hbe : P.edge e = b) (hbf : P.edge f = b) : e = f := by
  by_contra hn
  have hEq : D.edgeCarrier e = D.edgeCarrier f := by
    calc
      D.edgeCarrier e = D.copyCarrier i ∩ P.strip b :=
        (P.copy_absorption i b e he hbe).symm
      _ = D.edgeCarrier f := P.copy_absorption i b f hf hbf
  obtain ⟨x,hx,y,hy,hxy⟩ := hsize
  rw [← hbe,← P.edge_image e] at hx hy
  obtain ⟨u,hu,hu'⟩ := hx
  obtain ⟨w,hw,hw'⟩ := hy
  have h := hlin e f hn ⟨hu,hEq ▸ hu⟩ ⟨hw,hEq ▸ hw⟩
  exact hxy (hu'.symm.trans ((congrArg P.vertex h).trans hw'))

/-- The active strip has girth greater than m, even if the entire
picture has much smaller edge girth. Complete the at most m
owners of a purported short cycle and use the marked-edge lemma. -/
theorem strip_girth_of_qualitativeCompletion
    (b : B) (hsize : (base b).Nontrivial)
    (hlin : ∀ e f, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hpair : D.bottomCut.ZeroPairwise)
    (hCover : D.CopyCovered) (m : ℕ)
    (hcomp : ContactCompletable D.copyCarrier m) :
    LabelledGirthGT (P.stripHypergraph b).edgeCarrier m := by
  classical
  rintro ⟨C,hC⟩
  let c (k : Fin C.length) : I := Classical.choose (hCover.2 (C.label k).val)
  have hc (k : Fin C.length) : (C.label k).val ∈ D.copyEdges (c k) :=
    Classical.choose_spec (hCover.2 (C.label k).val)
  let s : Finset I := Finset.univ.image c
  have hs : s.Nonempty := by
    let k : Fin C.length := ⟨0,by have := C.hlength; omega⟩
    exact ⟨c k,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩
  have hb : s.card ≤ m := by
    calc
      s.card ≤ (Finset.univ : Finset (Fin C.length)).card := Finset.card_image_le
      _ = C.length := by simp
      _ ≤ m := hC
  obtain ⟨t,hst,⟨J⟩⟩ := hcomp s hs hb
  let Q := {i : I // i ∈ t}
  let C' : LabelledBergeCycle (fun e : P.StripEdge b => D.edgeCarrier e.val) := {
    length := C.length
    hlength := C.hlength
    label := C.label
    vertex := fun k => (C.vertex k).val
    label_injective := C.label_injective
    vertex_injective := fun i j h => C.vertex_injective (Subtype.ext h)
    left_mem := C.left_mem
    right_mem := C.right_mem }
  apply contact_marked_cycle_impossible (Q := Q)
    (fun i : Q => D.copyCarrier i.val) D.edgeCarrier
    (fun i : Q => D.copyEdges i.val) (fun e => P.edge e = b) J
    (fun i e he => P.copy_edge_subset i.val e he)
    ?_ hlin ?_ C' ?_
  · intro i e f he hf hbe hbf
    exact P.marked_edge_unique b hsize hlin i.val e f he hf hbe hbf
  · intro i j hne
    exact hpair (Sum.inl i.val) (Sum.inl j.val)
      (fun he => hne (Subtype.ext (Sum.inl.inj he)))
  · intro k
    exact ⟨⟨c k,hst (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)⟩,hc k⟩

end ContactBaseProjection

namespace ContactTrainPicture
variable {D : ContactHypergraphData V E I} {T : ContactTrainData E 1}
    {base : B → Set X} [LinearOrder V] [LinearOrder X]
    {allowed : Fin 1 → Set X} {q : Fin 2 → ℕ}
    (P : ContactTrainPicture D T base allowed q)

def OuterInvariant (m : ℕ) : Prop :=
  P.graph.CopyCovered ∧ P.graph.bottomCut.ZeroPairwise ∧
    ContactCompletable P.graph.copyCarrier m

namespace Core
variable {P} {b : B} (C : P.Core b)
    (hne : Nonempty (P.projection.StripEdge b))

/-- The image of every vertex and edge of the core lies in a
standard whenever the core is covered by its designated copies.
The old designated family covers all those standards. -/
theorem next_copyCovered
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < 1 → 2 ≤ q μ)
    (hP : P.graph.CopyCovered) (hC : C.graph.CopyCovered) :
    (C.next hne hbase hq).graph.CopyCovered := by
  let A := C.gluing hne
  have hv (i : C.Copy) (x : P.Vertex) :
      ∃ j : C.Copy × P.Copy, A.stdV i x ∈ A.outputHypergraph.copyCarrier j := by
    obtain ⟨j,hj⟩ := hP.1 x
    exact ⟨(i,j),⟨x,hj,rfl⟩⟩
  have he (i : C.Copy) (e : P.Edge) :
      ∃ j : C.Copy × P.Copy, A.stdE i e ∈ A.outputHypergraph.copyEdges j := by
    obtain ⟨j,hj⟩ := hP.2 e
    exact ⟨(i,j),⟨e,hj,rfl⟩⟩
  constructor
  · intro x
    rcases contactGlued_cover A.vertexGlue A.vertex_inj x with ⟨u,rfl⟩ | ⟨i,u,rfl⟩
    · obtain ⟨i,hi⟩ := hC.1 u
      obtain ⟨v,hv'⟩ := (A.vertex_domain i u).mpr hi
      have hEq := (contactStandardEmb_eq_core A.vertexGlue A.vertex_inj i v u).mpr hv'
      rw [← hEq]
      exact hv i v
    · exact hv i u
  · intro e
    rcases contactGlued_cover A.edgeGlue A.edge_inj e with ⟨f,rfl⟩ | ⟨i,f,rfl⟩
    · obtain ⟨i,hi⟩ := hC.2 f
      obtain ⟨v,he'⟩ := (A.edge_domain i f).mpr hi
      have hEq := (contactStandardEmb_eq_core A.edgeGlue A.edge_inj i v f).mpr he'
      rw [← hEq]
      exact he i v
    · exact he i f

theorem next_pairwise
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < 1 → 2 ≤ q μ)
    (hP : P.graph.bottomCut.ZeroPairwise) :
    (C.next hne hbase hq).graph.bottomCut.ZeroPairwise :=
  (C.gluing hne).output_pairwise_of_trace P.projection b
    (C.family.stripGluing_active hne) hbase C.linear hP

end Core
end ContactTrainPicture
end StructuralRamsey.Girth
