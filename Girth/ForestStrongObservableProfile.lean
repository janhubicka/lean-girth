import Girth.ForestObservableForestColour
import Girth.LocalForestPieces

/-!
# Actual strong support B-copies have a finite complete forest profile

For any q marked strong support embeddings of one source hypergraph H,
their vertex images are jointly marked by Fin q × X, and their intrinsic
A-edges have a fixed labelled pattern independent of the target host.

Consequently the abstract marked-support presentation assumptions needed
for complete forest-profile invariance hold *automatically*. Two q-tuples
of strong support copies with the same finite observable equality profile
are either both forests or both nonforests, including the complete
running-intersection join-tree condition.

No assumption of a bounded ancestral history or shape-map equivariance
is involved. This is exactly the semantic finite-palette interface.
-/

namespace StructuralRamsey.Girth

/-- The jointly labelled vertices of q strong support embeddings. -/
def strongMarkedVertex
    (q : ℕ) {X W : Type}
    {H : Set (Set X)} {K : Set (Set W)}
    (family : Fin q → StrongSupportEmbedding H K) :
    MarkedCopyVertex q X → W :=
  fun p => family p.1 p.2

/-- Fixed formal positions belonging to the ith source B-copy. -/
def strongMarkedCarrier (q : ℕ) (X : Type)
    (i : Fin q) : Set (MarkedCopyVertex q X) :=
  {p | p.1 = i}

/-- The fixed formal A-support atoms inside the ith copy. -/
def strongMarkedAtoms (q : ℕ) {X : Type}
    (H : Set (Set X)) (i : Fin q) :
    Set (Set (MarkedCopyVertex q X)) :=
  {a | ∃ e ∈ H, a = {p | p.1 = i ∧ p.2 ∈ e}}

/-- Actual strong copy carriers are the evaluations of their labelled
positions. This is also true for arbitrary (possibly infinite) sources. -/
theorem strongSupport_carrier_eq_marked_image
    (q : ℕ) {X W : Type}
    {H : Set (Set X)} {K : Set (Set W)}
    (family : Fin q → StrongSupportEmbedding H K)
    (i : Fin q) :
    (family i).supportPiece.carrier =
      strongMarkedVertex q family '' strongMarkedCarrier q X i := by
  change Set.range (family i) =
    strongMarkedVertex q family '' strongMarkedCarrier q X i
  ext y
  constructor
  · rintro ⟨x, hEq⟩
    exact ⟨(i, x), rfl, hEq⟩
  · rintro ⟨⟨j, x⟩, hj, hEq⟩
    change j = i at hj
    subst j
    exact ⟨x, hEq⟩

/-- Mapping a formally tagged source edge gives exactly its image
under the corresponding selected strong support embedding. -/
theorem strongMarked_image_atom
    (q : ℕ) {X W : Type}
    {H : Set (Set X)} {K : Set (Set W)}
    (family : Fin q → StrongSupportEmbedding H K)
    (i : Fin q) (e : Set X) :
    strongMarkedVertex q family ''
      {p : MarkedCopyVertex q X | p.1 = i ∧ p.2 ∈ e} =
        (family i) '' e := by
  ext y
  constructor
  · rintro ⟨⟨j, x⟩, ⟨hj, hx⟩, hEq⟩
    subst j
    exact ⟨x, hx, hEq⟩
  · rintro ⟨x, hx, hEq⟩
    exact ⟨(i, x), ⟨rfl, hx⟩, hEq⟩

/-- Every source support edge of a strong copy is represented by an
image of the fixed labelled intrinsic atom; no extra local A-edges
are silently inserted in this supportPiece presentation. -/
theorem strongSupport_edges_eq_marked_atoms
    (q : ℕ) {X W : Type}
    {H : Set (Set X)} {K : Set (Set W)}
    (family : Fin q → StrongSupportEmbedding H K)
    (i : Fin q) (e : Set W) :
    e ∈ (family i).supportPiece.edges ↔
      ∃ a ∈ strongMarkedAtoms q H i,
        e = strongMarkedVertex q family '' a := by
  constructor
  · rintro ⟨e0, he0, hEq⟩
    refine ⟨{p : MarkedCopyVertex q X |
        p.1 = i ∧ p.2 ∈ e0}, ⟨e0, he0, rfl⟩, ?_⟩
    calc
      e = (family i) '' e0 := hEq
      _ = strongMarkedVertex q family ''
          {p : MarkedCopyVertex q X |
            p.1 = i ∧ p.2 ∈ e0} :=
        (strongMarked_image_atom q family i e0).symm
  · rintro ⟨a, ⟨e0, he0, hA⟩, hEq⟩
    subst a
    refine ⟨e0, he0, ?_⟩
    calc
      e = strongMarkedVertex q family ''
          {p : MarkedCopyVertex q X |
            p.1 = i ∧ p.2 ∈ e0} := hEq
      _ = (family i) '' e0 :=
        strongMarked_image_atom q family i e0

/-- The full abstract marked presentation is automatically realised
by any two q-families of strong embeddings of the same support H. -/
theorem strongSupport_sameMarkedPresentation
    (q : ℕ) {X W Z : Type}
    {H : Set (Set X)}
    {K : Set (Set W)} {L : Set (Set Z)}
    (f : Fin q → StrongSupportEmbedding H K)
    (g : Fin q → StrongSupportEmbedding H L) :
    SameMarkedSupportPresentation
      (fun i => (f i).supportPiece)
      (fun i => (g i).supportPiece)
      (strongMarkedVertex q f) (strongMarkedVertex q g)
      (strongMarkedCarrier q X)
      (strongMarkedAtoms q H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact strongSupport_carrier_eq_marked_image q f i
  · intro i
    exact strongSupport_carrier_eq_marked_image q g i
  · intro i e
    exact strongSupport_edges_eq_marked_atoms q f i e
  · intro i e
    exact strongSupport_edges_eq_marked_atoms q g i e

/-- A COMPLETE finite observable-profile invariance theorem for actual
q-tuples of strong copies, with no abstract presentation hypotheses.
The common role alphabet can encode base projection, ports and births. -/
theorem strongSupport_forest_iff_of_sameObservableProfile
    (q : ℕ) {X W Z Role : Type}
    {H : Set (Set X)}
    {K : Set (Set W)} {L : Set (Set Z)}
    [DecidableEq W] [DecidableEq Z]
    (f : Fin q → StrongSupportEmbedding H K)
    (g : Fin q → StrongSupportEmbedding H L)
    (role : MarkedCopyVertex q X → Role)
    (hProfile :
      forestObservableProfile q (strongMarkedVertex q f) role =
      forestObservableProfile q (strongMarkedVertex q g) role) :
    ForestOfCopies (fun i => (f i).supportPiece) ↔
      ForestOfCopies (fun i => (g i).supportPiece) := by
  exact forestObservableProfile_determines_forest
    q (strongMarkedVertex q f) (strongMarkedVertex q g)
      role hProfile
    (fun i => (f i).supportPiece)
    (fun i => (g i).supportPiece)
    (strongMarkedCarrier q X)
    (strongMarkedAtoms q H)
    (strongSupport_sameMarkedPresentation q f g)

end StructuralRamsey.Girth
