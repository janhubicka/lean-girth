import Girth.Berge

/-!
# The order-one cycle argument, with actual edge probes

An order-one big cycle has exactly two occurrences, one vertex connector,
and one wagon connector. Distinctness of the connectors is automatic since
they have different kinds. A2 and A3 are automatic at length two; A1 says
that at least one label is designated. Its mixed boundaries prohibit a long
replacement, so a designated label is supreme precisely when it contains an
edge of the specified wagon through the specified vertex.

The definitions below are this exact order-one fragment, not a new
assumption that bridges already exist. They retain the disjoint sum of
designated and edge labels even when their carriers coincide. The main
proof first obtains one supreme label and then probes with its actual edge
to force the other designated label to be supreme as well.

No higher-order cycle, wagon linearity, or Ramsey existence theorem is
asserted here. Those parts of system girth remain separate.
-/

namespace StructuralRamsey.Girth

universe v

/-- Incidence data needed by the order-one fragment of a pretrain system.
No vertex-carrier injectivity is imposed on either sort of labels. -/
structure OrderOneData (V E I P : Type v) where
  edgeCarrier : E → Set V
  copyCarrier : I → Set V
  copyEdges : I → Set E
  parent : E → P

namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

def carrier : I ⊕ E → Set V
  | .inl i => D.copyCarrier i
  | .inr e => D.edgeCarrier e

def edges : I ⊕ E → Set E
  | .inl i => D.copyEdges i
  | .inr e => {e}

def designated (_ : OrderOneData V E I P) : I ⊕ E → Prop
  | .inl _ => True
  | .inr _ => False

def Meets (a : I ⊕ E) (p : P) : Prop :=
  ∃ e, e ∈ D.edges a ∧ D.parent e = p

/-- Exactly a short piece with mixed boundary connectors x and p. -/
def Bridge (a : I ⊕ E) (x : V) (p : P) : Prop :=
  ∃ e, e ∈ D.edges a ∧ D.parent e = p ∧ x ∈ D.edgeCarrier e

/-- Exactly the acceptable cycles A x B W of order one. -/
structure Cycle where
  left : I ⊕ E
  right : I ⊕ E
  vertex : V
  wagon : P
  different : left ≠ right
  left_vertex : vertex ∈ D.carrier left
  right_vertex : vertex ∈ D.carrier right
  left_meets : D.Meets left wagon
  right_meets : D.Meets right wagon
  has_designated : D.designated left ∨ D.designated right

/-- With mixed boundaries only a short replacement is possible. -/
def Cycle.HasSupreme (C : D.Cycle) : Prop :=
  (D.designated C.left ∧ D.Bridge C.left C.vertex C.wagon) ∨
  (D.designated C.right ∧ D.Bridge C.right C.vertex C.wagon)

def Bound : Prop := ∀ C : D.Cycle, C.HasSupreme

/-- An actual edge label supplies its own bridge. -/
theorem edge_bridge (e : E) (x : V) (p : P)
    (hx : x ∈ D.carrier (.inr e)) (hm : D.Meets (.inr e) p) :
    D.Bridge (.inr e) x p := by
  rcases hm with ⟨f, hf, hp⟩
  have hfe : f = e := hf
  subst f
  exact ⟨e, rfl, hp, hx⟩

/-- Probing with an actual edge leaves only one possible supreme label. -/
theorem bridge_of_incident_edge (h : D.Bound)
    (a : I ⊕ E) (x : V) (p : P)
    (hx : x ∈ D.carrier a) (hm : D.Meets a p)
    (e : E) (hep : D.parent e = p) (hxe : x ∈ D.edgeCarrier e) :
    D.Bridge a x p := by
  cases a with
  | inr f => exact D.edge_bridge f x p hx hm
  | inl i =>
    let C : D.Cycle := {
      left := .inl i
      right := .inr e
      vertex := x
      wagon := p
      different := by intro h; cases h
      left_vertex := hx
      right_vertex := hxe
      left_meets := hm
      right_meets := ⟨e, rfl, hep⟩
      has_designated := Or.inl trivial }
    rcases h C with hs | hs
    · exact hs.2
    · exact False.elim hs.1

/-- Both distinct source labels have a bridge. The first supreme copy
provides an actual edge; probing forces the other bridge. -/
theorem both_bridges (h : D.Bound)
    (a b : I ⊕ E) (x : V) (p : P) (hne : a ≠ b)
    (ha : x ∈ D.carrier a) (hb : x ∈ D.carrier b)
    (hma : D.Meets a p) (hmb : D.Meets b p) :
    D.Bridge a x p ∧ D.Bridge b x p := by
  have seed : D.Bridge a x p ∨ D.Bridge b x p := by
    cases a with
    | inr e => exact Or.inl (D.edge_bridge e x p ha hma)
    | inl i =>
      let C : D.Cycle := {
        left := .inl i
        right := b
        vertex := x
        wagon := p
        different := hne
        left_vertex := ha
        right_vertex := hb
        left_meets := hma
        right_meets := hmb
        has_designated := Or.inl trivial }
      rcases h C with hs | hs
      · exact Or.inl hs.2
      · exact Or.inr hs.2
  rcases seed with ⟨e, _he, hep, hxe⟩ | ⟨e, _he, hep, hxe⟩
  · exact ⟨D.bridge_of_incident_edge h a x p ha hma e hep hxe,
      D.bridge_of_incident_edge h b x p hb hmb e hep hxe⟩
  · exact ⟨D.bridge_of_incident_edge h a x p ha hma e hep hxe,
      D.bridge_of_incident_edge h b x p hb hmb e hep hxe⟩

/-- Exact incidence characterization of the order-one system bound. -/
theorem bound_iff_both_bridges : D.Bound ↔
    ∀ (a b : I ⊕ E) (x : V) (p : P), a ≠ b →
      x ∈ D.carrier a → x ∈ D.carrier b →
      D.Meets a p → D.Meets b p →
      D.Bridge a x p ∧ D.Bridge b x p := by
  constructor
  · exact D.both_bridges
  · intro h C
    have hb := h C.left C.right C.vertex C.wagon C.different
      C.left_vertex C.right_vertex C.left_meets C.right_meets
    rcases C.has_designated with hl | hr
    · exact Or.inl ⟨hl, hb.1⟩
    · exact Or.inr ⟨hr, hb.2⟩

end OrderOneData
end StructuralRamsey.Girth
