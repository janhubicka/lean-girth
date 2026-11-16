import Girth.TrainFillingPrivateRealUnionColoured

set_option Elab.async false

/-!
# Why the raw relational first-wagon union is NOT a fully ordered target

The basic EHN free-amalgamation input W is formed by a relational
disjoint union. Its within-colour BINARY order relation is carried
ONLY by pairs in the SAME summand, though it also has a separate
auxiliary LinearOrder on all its vertices.

If two different first wagons have vertices of the SAME colour,
no induced relational embedding of that raw W into a
colouredOrderedEdgeTarget with a TOTAL within-colour order can exist:
the latter orders every pair, while W orders neither direction.

Therefore the source auxiliary LinearOrder must not be confused
with the actual binary L-relation. The ordered/marked Track 1
selected-family construction must explicitly justify passing from
the raw EHN input/output to full coloured ordered hypergraphs.
Merely reordering X or choosing a LinearOrder instance does not
supply this relational-order completion.

These are NEGATIVE GUARD lemmas. They do not refute the Ramsey
construction or add an output requirement. They prevent a false
shortcut when interpreting selected EHN W-copies.
The source is an uncompiled Lean candidate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- In the actual raw relational disjoint union, the binary
within-colour order relation NEVER compares vertices from
different summands, regardless of their auxiliary global order. -/
theorem rawFirstWagonUnion_no_cross_order
    {I : Type u} {V P : Type v} [LinearOrder V]
    (k : ℕ) (edges : Set (Set V)) (colour : V → I)
    (carrier : P → Set V)
    (p q : P) (hpq : p ≠ q)
    (x : {v : V // v ∈ carrier p})
    (y : {v : V // v ∈ carrier q}) :
    ¬ (firstWagonDisjointUnion carrier
        (fun r => (colouredOrderedEdgeTarget k edges colour).induce
          (carrier r))).rel
      (.inr ()) ![(⟨p, x⟩ : FirstWagonUnionVertex carrier),
                    (⟨q, y⟩ : FirstWagonUnionVertex carrier)] := by
  rintro ⟨r, t, hTuple, _hOrder⟩
  have hpr : p = r := congrArg Sigma.fst (hTuple 0)
  have hqr : q = r := congrArg Sigma.fst (hTuple 1)
  exact hpq (hpr.trans hqr.symm)

/-- A full within-colour order on X makes an induced embedding
of the *raw* W impossible whenever two distinct summands
contain same-colour vertices. The unary relations force
the two images to retain that same colour, and totality of
the X-order then creates a relation missing from raw W.

This is an explicit formal obstruction to treating a raw
free-amalgamation disjoint union as an ordered relational
structure merely by adding an auxiliary LinearOrder instance.
-/
theorem rawFirstWagonUnion_not_embeddable_in_full_order
    {I : Type u} {V X P : Type v}
    [LinearOrder V] [LinearOrder X]
    (k : ℕ) (edges : Set (Set V)) (colour : V → I)
    (carrier : P → Set V)
    (templateEdges : Set (Set X)) (templateColour : X → I)
    (p q : P) (hpq : p ≠ q)
    (x : {v : V // v ∈ carrier p})
    (y : {v : V // v ∈ carrier q})
    (hSame : colour x.1 = colour y.1)
    (f : Embedding
      (firstWagonDisjointUnion carrier
        (fun r => (colouredOrderedEdgeTarget k edges colour).induce
          (carrier r)))
      (colouredOrderedEdgeTarget k templateEdges templateColour)) :
    False := by
  let W := firstWagonDisjointUnion carrier
    (fun r => (colouredOrderedEdgeTarget k edges colour).induce
      (carrier r))
  let a : FirstWagonUnionVertex carrier := ⟨p, x⟩
  let b : FirstWagonUnionVertex carrier := ⟨q, y⟩
  have hColour (r : P) (z : {v : V // v ∈ carrier r}) :
      templateColour (f (⟨r, z⟩ : FirstWagonUnionVertex carrier)) =
        colour z.1 := by
    have hW : W.rel (.inl (.inr (colour z.1)))
        (fun _ : Fin 1 =>
          (⟨r, z⟩ : FirstWagonUnionVertex carrier)) := by
      refine ⟨r, (fun _ : Fin 1 => z), (by intro i; rfl), ?_⟩
      change colour z.1 = colour z.1
      rfl
    have hX := (f.map_rel_iff (.inl (.inr (colour z.1)))
      (fun _ : Fin 1 =>
        (⟨r, z⟩ : FirstWagonUnionVertex carrier))).mpr hW
    change templateColour (f (⟨r, z⟩ :
      FirstWagonUnionVertex carrier)) = colour z.1 at hX
    exact hX
  have hImagesSame :
      templateColour (f a) = templateColour (f b) := by
    calc
      templateColour (f a) = colour x.1 := hColour p x
      _ = colour y.1 := hSame
      _ = templateColour (f b) := (hColour q y).symm
  have hab : f a ≠ f b := by
    intro h
    exact hpq (congrArg Sigma.fst (f.injective h))
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hTarget :
        (colouredOrderedEdgeTarget k templateEdges templateColour).rel
          (.inr ()) ![f a, f b] := by
      change templateColour (f a) = templateColour (f b) ∧ f a < f b
      exact ⟨hImagesSame, hlt⟩
    have hSource := (f.map_rel_iff (.inr ()) ![a, b]).mp hTarget
    exact rawFirstWagonUnion_no_cross_order k edges colour
      carrier p q hpq x y hSource
  · have hTarget :
        (colouredOrderedEdgeTarget k templateEdges templateColour).rel
          (.inr ()) ![f b, f a] := by
      change templateColour (f b) = templateColour (f a) ∧ f b < f a
      exact ⟨hImagesSame.symm, hgt⟩
    have hSource := (f.map_rel_iff (.inr ()) ![b, a]).mp hTarget
    exact rawFirstWagonUnion_no_cross_order k edges colour
      carrier q p (Ne.symm hpq) y x hSource

end StructuralRamsey.Girth
