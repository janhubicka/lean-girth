import Girth.TrainFillingTemplateConstruction

set_option Elab.async false

/-!
# The physical edge-token part of forbidden-predicate splitting

Each forbidden-predicate vertex is split according to the actual physical
edge containing it; allowed-predicate vertices are retained. The edge image
retains every old carrier and no distinct old physical edges are identified.
Any intersection of two distinct split edges lies in an allowed predicate.

This is not yet the complete coloured Ramsey input: lifting selected ordered,
strongly induced B-copies, including isolated source vertices, and transferring
the selected Ramsey arrow are separate tasks.
-/

namespace StructuralRamsey.Girth

universe v

structure ColouredEdgeOwnerSplit (V I : Type v) where
  edges : Set (Set V)
  predicate : V → I
  allowed : Set I

namespace ColouredEdgeOwnerSplit

variable {V I : Type v} (H : ColouredEdgeOwnerSplit V I)

abbrev OldEdge := {e : Set V // e ∈ H.edges}
abbrev Vertex := V ⊕ (V × (H.OldEdge ⊕ PUnit))

def project : H.Vertex → V
  | .inl x => x
  | .inr (x, _) => x

/-- The split retains the exact original unary predicate of every vertex. -/
def newPredicate (z : H.Vertex) : I := H.predicate (H.project z)

/-- A vertex on physical edge e has a unique incidence token when its
predicate is forbidden; in allowed predicates it keeps its old name. -/
noncomputable def place (e : H.OldEdge) (x : V) : H.Vertex := by
  classical
  exact if H.predicate x ∈ H.allowed then .inl x
    else .inr (x, .inl e)

@[simp] theorem project_place (e : H.OldEdge) (x : V) :
    H.project (H.place e x) = x := by
  classical
  by_cases h : H.predicate x ∈ H.allowed <;>
    simp [place, project, h]

@[simp] theorem newPredicate_place (e : H.OldEdge) (x : V) :
    H.newPredicate (H.place e x) = H.predicate x := by
  simp only [newPredicate, project_place]

theorem place_injective (e : H.OldEdge) : Function.Injective (H.place e) := by
  intro x y h
  have hproj := congrArg H.project h
  simpa only [project_place] using hproj

/-- A split edge is the image of all and only its old endpoints. -/
noncomputable def splitEdge (e : H.OldEdge) : Set H.Vertex :=
  H.place e '' e.1

theorem projection_splitEdge (e : H.OldEdge) :
    H.project '' H.splitEdge e = e.1 := by
  ext x
  constructor
  · rintro ⟨z, ⟨y, hy, hzy⟩, hzx⟩
    subst z
    have hyx : y = x := (H.project_place e y).symm.trans hzx
    simpa only [hyx] using hy
  · intro hx
    exact ⟨H.place e x, ⟨x, hx, rfl⟩, H.project_place e x⟩

/-- The edge-token representation never identifies two distinct old
physical edges (which are already indexed by their actual carrier sets). -/
theorem splitEdge_injective : Function.Injective H.splitEdge := by
  intro e f hef
  apply Subtype.ext
  calc
    e.1 = H.project '' H.splitEdge e := (H.projection_splitEdge e).symm
    _ = H.project '' H.splitEdge f :=
      congrArg (fun s : Set H.Vertex => H.project '' s) hef
    _ = f.1 := H.projection_splitEdge f

/-- All contacts between different physical split edges occur in
predicates where incidences were allowed to be shared. -/
theorem intersection_only_allowed
    (e f : H.OldEdge) (hef : e ≠ f)
    (z : H.Vertex) (he : z ∈ H.splitEdge e) (hf : z ∈ H.splitEdge f) :
    ∃ x : V, H.predicate x ∈ H.allowed ∧ z = Sum.inl x := by
  classical
  obtain ⟨x, hx, hzx⟩ := he
  obtain ⟨y, hy, hzy⟩ := hf
  have hxy : x = y := by
    have hp := congrArg H.project (hzx.trans hzy.symm)
    simpa only [H.project_place] using hp
  subst y
  by_cases h : H.predicate x ∈ H.allowed
  · refine ⟨x, h, ?_⟩
    have hs : H.place e x = Sum.inl x := by simp [H.place, h]
    exact hzx.symm.trans hs
  · have hs : H.place e x = H.place f x := hzx.trans hzy.symm
    have hs' :
        (Sum.inr (x, Sum.inl e) : H.Vertex) =
          Sum.inr (x, Sum.inl f) := by
      simpa [H.place, h] using hs
    have hpair : (x, Sum.inl e) = (x, Sum.inl f) := Sum.inr.inj hs'
    have heq : e = f := Sum.inl.inj (Prod.mk.inj hpair).2
    exact False.elim (hef heq)

/-- Keep a separate bottom token for isolated vertices in forbidden
predicates, so later lifted copies can retain their full vertex set. -/
noncomputable def isolatedLift (x : V) : H.Vertex := by
  classical
  exact if H.predicate x ∈ H.allowed then .inl x
    else .inr (x, .inr PUnit.unit)

@[simp] theorem project_isolatedLift (x : V) :
    H.project (H.isolatedLift x) = x := by
  classical
  by_cases h : H.predicate x ∈ H.allowed <;>
    simp [isolatedLift, project, h]

@[simp] theorem newPredicate_isolatedLift (x : V) :
    H.newPredicate (H.isolatedLift x) = H.predicate x := by
  simp only [newPredicate, project_isolatedLift]

theorem isolatedLift_injective : Function.Injective H.isolatedLift := by
  intro x y h
  have hp := congrArg H.project h
  simpa only [project_isolatedLift] using hp

end ColouredEdgeOwnerSplit
end StructuralRamsey.Girth
