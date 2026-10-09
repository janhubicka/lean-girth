import Girth.ForestTwoCopyPortGlue
import Girth.ForestAttach
import Mathlib.Tactic

/-!
# A safe one-port clone attached to an entire old B-copy forest

The explicit two-copy separator model can attach a fresh private copy
of one selected old B-piece to a whole forest of previously designated
B-pieces. Every old vertex is retained in the left image and the new
piece occupies the right image, glued only along one port S of its
chosen old owner.

The new piece's intersection with EVERY unrelated old piece is
contained in its intersection with the chosen owner. Consequently
the old join tree can be extended by one leaf whenever all new/old
pair intersections are allowed. For an empty or singleton port they
are automatically allowed, so this gives an unconditional
one-vertex safe geometric fan-out step.

For a complete A-edge port, allowed intersections with unrelated
old members require support-inducedness/closure; they are not
silently assumed here. This is one step of a safe geometric
reservoir, not the whole successor-tree Ramsey construction.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- Any intersection between an old left picture and a fresh right
picture lies among the prescribed old port vertices, regardless of
how large either carrier is. -/
theorem twoCopyPort_cross_inter_subset
    (S A B : Set W) :
    (twoCopyPortLeft S) '' A ∩ (twoCopyPortRight S) '' B ⊆
      (twoCopyPortLeft S) '' S := by
  rintro z ⟨⟨x, _, hx⟩, ⟨y, _, hy⟩⟩
  have hxy : twoCopyPortLeft S x = twoCopyPortRight S y :=
    hx.trans hy.symm
  exact ⟨x, ((twoCopyPort_cross_eq_iff S x y).mp hxy).2, hx⟩

/-- A fresh right copy has no contact with any old left piece
outside the old port; its contacts are dominated by the selected
old owner whenever S is inside that owner's carrier. -/
theorem twoCopyPort_clone_contacts_dominated
    (Y : I → HypergraphPiece W) (p i : I)
    (S : Set W) (hSub : S ⊆ (Y p).carrier) :
    ((Y p).map (twoCopyPortRight S)).carrier ∩
      ((Y i).map (twoCopyPortLeft S)).carrier ⊆
    ((Y p).map (twoCopyPortRight S)).carrier ∩
      ((Y p).map (twoCopyPortLeft S)).carrier := by
  intro z hz
  have hSep : z ∈ (twoCopyPortLeft S) '' S := by
    apply twoCopyPort_cross_inter_subset S
      (Y i).carrier (Y p).carrier
    exact ⟨hz.2, hz.1⟩
  obtain ⟨x, hx, hxz⟩ := hSep
  refine ⟨hz.1, ?_⟩
  exact ⟨x, hSub hx, hxz⟩

/-- Adding one private clone to an arbitrary old forest preserves
the full running-intersection join tree when cross overlaps are
permitted. The new copy is attached as a leaf at its owner. -/
theorem twoCopyPort_fanout_of_allowed
    [Fintype I] [Nonempty I]
    {Y : I → HypergraphPiece W}
    (hY : ForestOfCopies Y) (p : I)
    (S : Set W) (hSub : S ⊆ (Y p).carrier)
    (hCross : ∀ i : I,
      AllowedIntersection
        ((Y i).map (twoCopyPortLeft S))
        ((Y p).map (twoCopyPortRight S))) :
    ForestOfCopies
      (sumPieces
        (fun i : I => (Y i).map (twoCopyPortLeft S))
        (fun _ : PUnit.{v+1} =>
          (Y p).map (twoCopyPortRight S))) := by
  have hOld : ForestOfCopies
      (fun i : I => (Y i).map (twoCopyPortLeft S)) :=
    hY.map (twoCopyPortLeft S)
  apply forestOfCopies_attach_dominated hOld
    ((Y p).map (twoCopyPortRight S)) hCross p
  intro i
  exact twoCopyPort_clone_contacts_dominated Y p i S hSub

/-- The physical overlap between any old left member and a new
right member is subsingleton when the port S is empty or a
singleton. This requires no A-strongness assumption. -/
theorem twoCopyPort_singleton_cross_allowed
    (P Q : HypergraphPiece W)
    (S : Set W) (hSmall : S.Subsingleton) :
    AllowedIntersection
      (P.map (twoCopyPortLeft S))
      (Q.map (twoCopyPortRight S)) := by
  left
  intro z hz t ht
  have hzS :
      z ∈ (twoCopyPortLeft S) '' S :=
    twoCopyPort_cross_inter_subset S P.carrier Q.carrier hz
  have htS :
      t ∈ (twoCopyPortLeft S) '' S :=
    twoCopyPort_cross_inter_subset S P.carrier Q.carrier ht
  obtain ⟨x, hx, hxz⟩ := hzS
  obtain ⟨y, hy, hyt⟩ := htS
  calc
    z = twoCopyPortLeft S x := hxz.symm
    _ = twoCopyPortLeft S y :=
      congrArg (twoCopyPortLeft S) (hSmall hx hy)
    _ = t := hyt

/-- Unconditional safe one-vertex (or empty-port) B-copy fan-out:
every old designated forest admits a new private copy of one
member over a chosen vertex, still forming a forest. -/
theorem twoCopyPort_singleton_fanout
    [Fintype I] [Nonempty I]
    {Y : I → HypergraphPiece W}
    (hY : ForestOfCopies Y) (p : I)
    (S : Set W)
    (hSub : S ⊆ (Y p).carrier)
    (hSmall : S.Subsingleton) :
    ForestOfCopies
      (sumPieces
        (fun i : I => (Y i).map (twoCopyPortLeft S))
        (fun _ : PUnit.{v+1} =>
          (Y p).map (twoCopyPortRight S))) := by
  exact twoCopyPort_fanout_of_allowed hY p S hSub
    (fun i => twoCopyPort_singleton_cross_allowed
      (Y i) (Y p) S hSmall)

end StructuralRamsey.Girth
