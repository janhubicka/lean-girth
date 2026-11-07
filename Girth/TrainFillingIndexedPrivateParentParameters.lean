import Girth.TrainFillingIndexedHigherCutPrivateGirth
import Girth.TrainParameterRestriction

set_option Elab.async false

/-!
# Adjacent wagon parent parameters survive private first-wagon filling

At any fixed cut, the only potentially shared vertices of DISTINCT
expanded quotient wagons are original OLD vertices: a genuinely
private vertex belongs to the quotient class of its single owner.

If the original μ-child wagon carriers satisfy the adjacent
μ→ν parent-intersection restriction, the expanded quotient wagons
satisfy the SAME restriction, with their allowed set embedded as
old vertices. This is stronger than allowing all private vertices
of some allowed predicate: no private vertex can occur in a sibling
intersection in the first place.

This local result is independent of the girth bound. A separate
choice-tagged quotient equivalence and commuting parent square
are still needed to state it as the full contracted M parameter
bound across all choices, especially at the universal top.
-/

namespace StructuralRamsey.Girth

universe v
variable {V Z Q R : Type v}

/-- Private extension cannot introduce a forbidden sibling overlap
at any parent level, provided old incidences remain exact and every
private vertex belongs to at most one child label. -/
theorem trainParentBound_of_unique_private
    (old : Q → Set V) (expanded : Q → Set (V ⊕ Z))
    (parent : Q → R) (allowed : Set V)
    (hOldMem : ∀ q : Q, ∀ x : V,
      Sum.inl x ∈ expanded q ↔ x ∈ old q)
    (hPrivate : ∀ q r : Q, ∀ z : Z,
      Sum.inr z ∈ expanded q →
      Sum.inr z ∈ expanded r → q = r)
    (hOld : TrainParentIntersectionBound old parent allowed) :
    TrainParentIntersectionBound expanded parent
      ((Sum.inl : V → V ⊕ Z) '' allowed) := by
  intro q r hqr hParent z hz
  cases z with
  | inl x =>
      have hAllowed : x ∈ allowed :=
        hOld hqr hParent
          ⟨(hOldMem q x).mp hz.1, (hOldMem r x).mp hz.2⟩
      exact ⟨x, hAllowed, rfl⟩
  | inr x =>
      exact False.elim
        (hqr (hPrivate q r x hz.1 hz.2))

/-- Parent/sibling overlap bounds also pass through a genuinely
DEPENDENT choice-tagged union. A common parent below the universal
top forces equal choice tags; different choice tags cannot have any
common vertex. All quotient occurrence labels remain distinct. -/
theorem trainParentBound_dependentTagged
    {C Q R : Type v} {W : C → Type v}
    (H : ∀ c : C, Q → Set (W c))
    (parent : Q → R)
    (allowed : ∀ c : C, Set (W c))
    (hLocal : ∀ c : C,
      TrainParentIntersectionBound (H c) parent (allowed c)) :
    TrainParentIntersectionBound
      (dependentTaggedCarriers H)
      (fun cq : C × Q => (cq.1, parent cq.2))
      {z : Sigma W | z.2 ∈ allowed z.1} := by
  rintro ⟨c, q⟩ ⟨d, r⟩ hDistinct hParent z hz
  have hcd : c = d := congrArg Prod.fst hParent
  subst d
  have hqr : q ≠ r := by
    intro h
    exact hDistinct (congrArg (Prod.mk c) h)
  obtain ⟨x, hx, hxEq⟩ := hz.1
  obtain ⟨y, hy, hyEq⟩ := hz.2
  have hxy : x = y :=
    dependentTagVertex_injective c (hxEq.trans hyEq.symm)
  have hAllowed : x ∈ allowed c :=
    hLocal c hqr (congrArg Prod.snd hParent)
      ⟨hx, by simpa only [hxy] using hy⟩
  rw [← hxEq]
  exact hAllowed


/-- At the universal parent, different choices can have the SAME
parent.  Nevertheless their tagged vertex carriers are disjoint.
For labels in one choice, a pairwise local overlap bound suffices
without any parent-tag condition.  This is the missing top-parent
case of dependent tagged unions. -/
theorem dependentTagged_pairwise_intersection
    {C Q : Type v} {W : C → Type v}
    (H : ∀ c : C, Q → Set (W c))
    (allowed : ∀ c : C, Set (W c))
    (hLocal : ∀ c : C, ∀ ⦃q r : Q⦄, q ≠ r →
      H c q ∩ H c r ⊆ allowed c)
    (a b : C × Q) (hab : a ≠ b) :
    dependentTaggedCarriers H a ∩ dependentTaggedCarriers H b ⊆
      {z : Sigma W | z.2 ∈ allowed z.1} := by
  rcases a with ⟨c, q⟩
  rcases b with ⟨d, r⟩
  intro z hz
  obtain ⟨x, hx, hxEq⟩ := hz.1
  obtain ⟨y, hy, hyEq⟩ := hz.2
  have hcd : c = d := congrArg Sigma.fst (hxEq.trans hyEq.symm)
  subst d
  have hqr : q ≠ r := by
    intro h
    exact hab (congrArg (Prod.mk c) h)
  have hxy : x = y :=
    dependentTagVertex_injective c (hxEq.trans hyEq.symm)
  have hAllowed : x ∈ allowed c :=
    hLocal c hqr ⟨hx, by simpa only [hxy] using hy⟩
  rw [← hxEq]
  exact hAllowed

namespace PrivateWagonInput

variable {P X : Type v}
variable (U : PrivateWagonInput V P X)

/-- At every pair of wagon cuts μ≤ν, an original allowed-vertex
restriction on sibling μ-wagon intersections is inherited by the
full expanded X-private μ-wagon carriers. In particular, this
covers every ADJACENT pair needed for the shortened train. -/
theorem expandedWagonClass_parentBound
    {m : ℕ} (T : EdgeTrainLevels P m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (allowed : Set V)
    (hOld : TrainParentIntersectionBound
      (T.wagonClassCarrier U.oldCarrier μ)
      (T.wagonParent μ ν hμν) allowed) :
    TrainParentIntersectionBound
      (T.wagonClassCarrier
        (fun p => Set.range (U.place p)) μ)
      (T.wagonParent μ ν hμν)
      ((Sum.inl : V → U.Vertex) '' allowed) :=
  trainParentBound_of_unique_private
    (T.wagonClassCarrier U.oldCarrier μ)
    (T.wagonClassCarrier
      (fun p => Set.range (U.place p)) μ)
    (T.wagonParent μ ν hμν) allowed
    (fun q x => U.expandedWagonClass_old_iff T μ q x)
    (fun q r z => U.expandedWagonClass_private_unique T μ q r z)
    hOld

end PrivateWagonInput
end StructuralRamsey.Girth
