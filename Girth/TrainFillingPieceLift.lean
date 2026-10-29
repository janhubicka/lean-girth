import Girth.TrainFillingCarrierInvariant
import Girth.TrainSimultaneousSupreme

/-!
# Circulation Section 13: lifting actual pieces through a filling

The old and filled incidence systems below have the same vertices,
designated labels and wagon labels. Filled designated edges are precisely
the inverse image of the old designated edges under the prescribed cover
map, and the filled parent map is the old parent map after that cover map.

An old short piece with distinct boundary connectors lifts to an actual
filled short or long piece. The only new long case has two vertex
boundaries in one old edge and no filled ambient edge through both. Old
edge linearity forces any such filled pair edge, if it exists, to have
that old edge as its cover; this verifies designated source ownership.
An old long piece lifts to a filled long piece by pointwise coverage.

These are the local existence and source-membership parts of the filling
proof's lifting cases (i) and (ii). No freshness of inserted wagons,
projection/contraction, or global simultaneous-replacement legality is
assumed or concluded. Those remain necessary for full system girth.
-/

namespace StructuralRamsey.Girth.TrainFilling

universe v
variable {V I P : Type v}

/-- Actual old edges of the filling, identified by their carrier sets. -/
abbrev OldEdge (F : TrainFilling V) := {f : Set V // f ∈ F.oldEdges}

/-- Actual filled edges, identified by their carrier sets. -/
abbrev NewEdge (F : TrainFilling V) := {e : Set V // e ∈ F.newEdges}

variable (F : TrainFilling V)

/-- The old physical incidence system at one train coordinate. -/
def oldData (copyCarrier : I → Set V)
    (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P) :
    OrderOneData V F.OldEdge I P where
  edgeCarrier := fun f => f.1
  copyCarrier := copyCarrier
  copyEdges := copyEdges
  parent := parent

/-- The actual filling: designated edges are cover preimages and wagon
membership is inherited from the old cover. Ambient edges are retained. -/
def filledData (copyCarrier : I → Set V)
    (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P) :
    OrderOneData V F.NewEdge I P where
  edgeCarrier := fun e => e.1
  copyCarrier := copyCarrier
  copyEdges := fun i => {e | F.cover e ∈ copyEdges i}
  parent := fun e => parent (F.cover e)

/-- An actual filled edge through two distinct vertices of one old edge
must have that old edge as its prescribed cover. Old edge linearity is
the only uniqueness premise; no global cycle bound is used. -/
theorem cover_eq_of_two_vertices
    (hLinear : ∀ f g : F.OldEdge, f ≠ g → (f.1 ∩ g.1).Subsingleton)
    (e : F.NewEdge) (f : F.OldEdge) (x y : V)
    (hxy : x ≠ y) (hxe : x ∈ e.1) (hye : y ∈ e.1)
    (hxf : x ∈ f.1) (hyf : y ∈ f.1) : F.cover e = f := by
  by_contra hne
  exact hxy ((hLinear (F.cover e) f hne)
    ⟨F.contained e hxe, hxf⟩ ⟨F.contained e hye, hyf⟩)

variable (copyCarrier : I → Set V)
variable (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P)

/-- A filled ambient pair edge always projects to an old ambient pair
edge. The converse is generally false and is not used. -/
theorem filled_pairEdge_old (x y : V)
    (h : (F.filledData copyCarrier copyEdges parent).PairEdge x y) :
    (F.oldData copyCarrier copyEdges parent).PairEdge x y := by
  obtain ⟨e, hx, hy⟩ := h
  exact ⟨F.cover e, F.contained e hx, F.contained e hy⟩

/-- Every old long piece lifts to a genuine filled long piece with the
same boundary vertices and the same wagon. Pointwise covering supplies
the two filled edges, whose different old covers ensure distinctness. -/
theorem longPiece_lift (i : I) (q r : V ⊕ P)
    (h : (F.oldData copyCarrier copyEdges parent).LongPiece (.inl i) q r) :
    (F.filledData copyCarrier copyEdges parent).LongPiece (.inl i) q r := by
  obtain ⟨x, y, w, f, g, hq, hr, hf, hg, hfg,
    hfw, hgw, hxf, hyg, hNoPair⟩ := h
  obtain ⟨e, he, hxe⟩ := F.covering f x hxf
  obtain ⟨d, hd, hyd⟩ := F.covering g y hyg
  refine ⟨x, y, w, e, d, hq, hr, ?_, ?_, ?_, ?_, ?_, hxe, hyd, ?_⟩
  · change F.cover e ∈ copyEdges i
    simpa only [he] using hf
  · change F.cover d ∈ copyEdges i
    simpa only [hd] using hg
  · intro hed
    apply hfg
    exact he.symm.trans ((congrArg F.cover hed).trans hd)
  · change parent (F.cover e) = w
    simpa only [he] using hfw
  · change parent (F.cover d) = w
    simpa only [hd] using hgw
  · intro hPair
    exact hNoPair (F.filled_pairEdge_old copyCarrier copyEdges parent x y hPair)

/-- Lifting a chosen old short edge through two distinct vertex
boundaries. If a filled pair edge exists, linearity puts it in the correct
designated preimage. Otherwise covering supplies a legal long piece. -/
theorem vertex_shortPiece_lift
    (hLinear : ∀ f g : F.OldEdge, f ≠ g → (f.1 ∩ g.1).Subsingleton)
    (i : I) (f : F.OldEdge) (hf : f ∈ copyEdges i)
    (x y : V) (hxy : x ≠ y) (hxf : x ∈ f.1) (hyf : y ∈ f.1) :
    (F.filledData copyCarrier copyEdges parent).ShortPiece (.inl i)
      (.inl x) (.inl y) ∨
    (F.filledData copyCarrier copyEdges parent).LongPiece (.inl i)
      (.inl x) (.inl y) := by
  classical
  by_cases hPair : (F.filledData copyCarrier copyEdges parent).PairEdge x y
  · obtain ⟨e, hxe, hye⟩ := hPair
    have he := F.cover_eq_of_two_vertices hLinear e f x y hxy hxe hye hxf hyf
    left
    refine ⟨e, ?_, hxe, hye⟩
    change F.cover e ∈ copyEdges i
    simpa only [he] using hf
  · obtain ⟨e, he, hxe⟩ := F.covering f x hxf
    obtain ⟨d, hd, hyd⟩ := F.covering f y hyf
    right
    refine ⟨x, y, parent f, e, d, rfl, rfl, ?_, ?_, ?_, ?_, ?_, hxe, hyd, hPair⟩
    · change F.cover e ∈ copyEdges i
      simpa only [he] using hf
    · change F.cover d ∈ copyEdges i
      simpa only [hd] using hf
    · intro hed
      apply hPair
      refine ⟨e, hxe, ?_⟩
      simpa only [hed] using hyd
    · change parent (F.cover e) = parent f
      rw [he]
    · change parent (F.cover d) = parent f
      rw [hd]

/-- Every old short piece with distinct boundary connectors lifts to a
filled short or long piece. Mixed boundaries always lift to a short
piece; an old edge cannot meet two distinct wagon boundaries. -/
theorem shortPiece_lift
    (hLinear : ∀ f g : F.OldEdge, f ≠ g → (f.1 ∩ g.1).Subsingleton)
    (i : I) (q r : V ⊕ P) (hne : q ≠ r)
    (h : (F.oldData copyCarrier copyEdges parent).ShortPiece (.inl i) q r) :
    (F.filledData copyCarrier copyEdges parent).ShortPiece (.inl i) q r ∨
    (F.filledData copyCarrier copyEdges parent).LongPiece (.inl i) q r := by
  obtain ⟨f, hf, hq, hr⟩ := h
  change f ∈ copyEdges i at hf
  cases q with
  | inl x =>
      change x ∈ f.1 at hq
      cases r with
      | inl y =>
          change y ∈ f.1 at hr
          exact F.vertex_shortPiece_lift copyCarrier copyEdges parent
            hLinear i f hf x y (fun hxy => hne (congrArg Sum.inl hxy)) hq hr
      | inr w =>
          obtain ⟨g, hgf, hgw⟩ := hr
          have hEq : g = f := hgf
          subst g
          obtain ⟨e, he, hxe⟩ := F.covering f x hq
          left
          refine ⟨e, ?_, hxe, e, rfl, ?_⟩
          · change F.cover e ∈ copyEdges i
            simpa only [he] using hf
          · change parent (F.cover e) = w
            simpa only [he] using hgw
  | inr w =>
      obtain ⟨g, hgf, hgw⟩ := hq
      have hEq : g = f := hgf
      subst g
      cases r with
      | inl y =>
          change y ∈ f.1 at hr
          obtain ⟨e, he, hye⟩ := F.covering f y hr
          left
          refine ⟨e, ?_, ?_, hye⟩
          · change F.cover e ∈ copyEdges i
            simpa only [he] using hf
          · refine ⟨e, rfl, ?_⟩
            change parent (F.cover e) = w
            simpa only [he] using hgw
      | inr z =>
          obtain ⟨g, hgf, hgz⟩ := hr
          have hEq : g = f := hgf
          subst g
          exact False.elim (hne (congrArg Sum.inr (hgw.symm.trans hgz)))

end StructuralRamsey.Girth.TrainFilling
