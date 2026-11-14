import Girth.TrainFillingPrivateSummand
import Girth.TrainFillingIndexedChoiceCore

set_option Elab.async false

/-!
# The original target vertices and edges, with their choice tags

The direct cutoff-two proof uses T inside the s-th component of
M = disjoint union_s M_s. The original vertex v does NOT literally
live in M: its correct image is (s, Sum.inl v).

For every local first-wagon A-support edge, the selected template
image becomes exactly the corresponding original edge at the old
positions of the private filling. No arbitrary target-edge map or
unproved output strongness is needed for this identity.

Original edges here are indexed by their actual first wagon and
their local A-support carrier. The application must identify that
index with the genuine edge set of T, preserving all predicates,
orders, and train equivalence relations. That remains a separate
end-to-end obligation.

These declarations are candidates until exact-head Lean compilation.
-/

namespace StructuralRamsey.Girth

universe v

namespace SummandPrivateTemplate

variable {V P X : Type v} (T : SummandPrivateTemplate V P X)

/-- Exactly the original first-wagon physical edges, tagged by p,
with local carriers in the appropriate first-wagon subtype.
Different F_p need not have the same vertex count or edge type. -/
abbrev OriginalEdge :=
  Sigma fun p : P =>
    {e : Set {x : V // x ∈ T.oldCarrier p} //
      e ∈ (T.piece p).localEdges}

/-- The actual first-wagon selected X-edge, retaining the original
wagon owner p; the template edge set is the complete E(X). -/
noncomputable def originalSelectedEdge
    (e : T.OriginalEdge) : T.toPrivateWagonInput.Edge := by
  let a : {a : Set X // a ∈ T.templateEdges} :=
    ⟨(T.piece e.1).star '' e.2.1, by
      rw [← T.templateEdges_eq e.1]
      exact (T.piece e.1).map_edge e.2⟩
  exact (e.1, a)

/-- A selected original edge really belongs to the chosen target
edge family of the complete private filling. -/
theorem originalSelectedEdge_mem_target
    (e : T.OriginalEdge) :
    T.originalSelectedEdge e ∈ T.toPrivateWagonInput.targetEdges := by
  change T.originalSelectedEdge e |>.2 ∈
    T.toPrivateWagonInput.selectedEdges e.1
  exact ⟨e.2, rfl⟩

/-- The full physical carrier of a selected original edge in M[X]
is precisely the old vertex set of that original edge, embedded
by Sum.inl. All extra X-positions are private; none leaks into
this selected edge. -/
theorem originalSelectedEdge_carrier
    (e : T.OriginalEdge) :
    T.toPrivateWagonInput.edgeCarrier (T.originalSelectedEdge e) =
      (Sum.inl : V → T.toPrivateWagonInput.Vertex) ''
        (Subtype.val '' e.2.1) := by
  classical
  let U := T.toPrivateWagonInput
  change U.place e.1 '' ((T.piece e.1).star '' e.2.1) =
    (Sum.inl : V → U.Vertex) '' (Subtype.val '' e.2.1)
  ext z
  constructor
  · rintro ⟨x, ⟨w, hw, hstar⟩, hz⟩
    refine ⟨w.1, ⟨w, hw, rfl⟩, ?_⟩
    calc
      Sum.inl w.1 = U.place e.1 ((T.piece e.1).star w) :=
        (U.place_old e.1 w).symm
      _ = U.place e.1 x := congrArg (U.place e.1) hstar
      _ = z := hz
  · rintro ⟨v, ⟨w, hw, hval⟩, himage⟩
    refine ⟨(T.piece e.1).star w, ⟨w, hw, rfl⟩, ?_⟩
    calc
      U.place e.1 ((T.piece e.1).star w) = Sum.inl w.1 :=
        U.place_old e.1 w
      _ = Sum.inl v := congrArg Sum.inl hval
      _ = z := himage

/-- Distinct original physical first-wagon edges never collapse
under the selected template map. This uses only injectivity of
the genuine local embedding and distinct p labels. -/
theorem originalSelectedEdge_injective :
    Function.Injective T.originalSelectedEdge := by
  rintro ⟨p, a⟩ ⟨q, b⟩ hab
  have hpq : p = q := congrArg Prod.fst hab
  subst q
  have hImage :
      (T.piece p).star '' a.1 = (T.piece p).star '' b.1 :=
    congrArg (fun e : T.toPrivateWagonInput.Edge => e.2.1) hab
  have hAB : a = b := by
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      have hImageX : (T.piece p).star x ∈
          (T.piece p).star '' b.1 := by
        rw [← hImage]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := hImageX
      exact (T.piece p).star.injective hxy ▸ hy
    · intro hx
      have hImageX : (T.piece p).star x ∈
          (T.piece p).star '' a.1 := by
        rw [hImage]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := hImageX
      exact (T.piece p).star.injective hxy ▸ hy
  cases hAB
  rfl
end SummandPrivateTemplate
end StructuralRamsey.Girth
