import Girth.TrainFillingPieceLift

/-!
# A short piece can require a long lift

The old edge {0,1,2} is filled by {0,1} and {1,2}. The designated
target owns that old edge and hence both filled edges. The old short
piece with boundaries 0 and 2 has no filled short lift, but it does
have a filled long lift. This checks the genuinely necessary disjunction
in `shortPiece_lift` on concrete physical edges and covering data.
-/

namespace StructuralRamsey.Girth.TrainFillingPieceLiftRegression

def leftEdge : Set (Fin 3) := {0, 1}
def rightEdge : Set (Fin 3) := {1, 2}

/-- A genuine filling of one old three-vertex edge by a two-edge path. -/
def filling : TrainFilling (Fin 3) where
  oldEdges := {Set.univ}
  newEdges := {leftEdge, rightEdge}
  cover := fun _ => ⟨Set.univ, by simp⟩
  contained := by intro e x hx; trivial
  covering := by
    intro f x hx
    have hf : f = ⟨Set.univ, by simp⟩ := by
      apply Subtype.ext
      exact f.2
    fin_cases x
    · exact ⟨⟨leftEdge, by simp⟩, hf.symm, by simp [leftEdge]⟩
    · exact ⟨⟨leftEdge, by simp⟩, hf.symm, by simp [leftEdge]⟩
    · exact ⟨⟨rightEdge, by simp⟩, hf.symm, by simp [rightEdge]⟩

def old : OrderOneData (Fin 3) filling.OldEdge Unit Unit :=
  filling.oldData (fun _ => Set.univ) (fun _ => Set.univ) (fun _ => ())

def filled : OrderOneData (Fin 3) filling.NewEdge Unit Unit :=
  filling.filledData (fun _ => Set.univ) (fun _ => Set.univ) (fun _ => ())

/-- The example's old incidence system is a linear pretrain. -/
theorem old_linearPretrain : old.LinearPretrain := by
  constructor
  · intro e f hne
    exact False.elim (hne (Subtype.ext (show e.1 = f.1 from
      (show e.1 = Set.univ from e.2).trans (show f.1 = Set.univ from f.2).symm)))
  · intro p q hne
    exact False.elim (hne (Subsingleton.elim p q))

private theorem path_intersection_subsingleton :
    (leftEdge ∩ rightEdge).Subsingleton := by
  intro x hx y hy
  fin_cases x <;> fin_cases y <;> norm_num [leftEdge, rightEdge] at *

/-- The filled path is also a linear pretrain, so the phenomenon is not
caused by dropping the manuscript's linearity hypotheses. -/
theorem filled_linearPretrain : filled.LinearPretrain := by
  constructor
  · intro e f hne
    change (e.1 ∩ f.1).Subsingleton
    have he : e.1 = leftEdge ∨ e.1 = rightEdge := by
      have h := e.2
      change e.1 = leftEdge ∨ e.1 = rightEdge at h
      exact h
    have hf : f.1 = leftEdge ∨ f.1 = rightEdge := by
      have h := f.2
      change f.1 = leftEdge ∨ f.1 = rightEdge at h
      exact h
    rcases he with he | he <;> rcases hf with hf | hf
    · exact False.elim (hne (Subtype.ext (he.trans hf.symm)))
    · rw [he, hf]
      exact path_intersection_subsingleton
    · rw [he, hf, Set.inter_comm]
      exact path_intersection_subsingleton
    · exact False.elim (hne (Subtype.ext (he.trans hf.symm)))
  · intro p q hne
    exact False.elim (hne (Subsingleton.elim p q))

/-- The sole old edge is a short piece through 0 and 2. -/
theorem old_short : old.ShortPiece (.inl ()) (.inl 0) (.inl 2) := by
  refine ⟨⟨Set.univ, by simp [filling]⟩, ?_, ?_, ?_⟩
  · change True
    trivial
  · change (0 : Fin 3) ∈ (Set.univ : Set (Fin 3))
    trivial
  · change (2 : Fin 3) ∈ (Set.univ : Set (Fin 3))
    trivial

/-- No ambient filled edge contains both end vertices. -/
theorem no_filled_pair : ¬ filled.PairEdge 0 2 := by
  rintro ⟨e, hZero, hTwo⟩
  change (0 : Fin 3) ∈ e.1 at hZero
  change (2 : Fin 3) ∈ e.1 at hTwo
  have he : e.1 = leftEdge ∨ e.1 = rightEdge := by
    have h := e.2
    change e.1 = leftEdge ∨ e.1 = rightEdge at h
    exact h
  rcases he with he | he
  · rw [he] at hTwo
    norm_num [leftEdge] at hTwo
  · rw [he] at hZero
    norm_num [rightEdge] at hZero

/-- Consequently the old short piece has no filled short lift. -/
theorem no_filled_short : ¬ filled.ShortPiece (.inl ()) (.inl 0) (.inl 2) := by
  rintro ⟨e, _, hZero, hTwo⟩
  exact no_filled_pair ⟨e, hZero, hTwo⟩

/-- The two path edges give a legal long lift in the sole wagon. -/
theorem filled_long : filled.LongPiece (.inl ()) (.inl 0) (.inl 2) := by
  let e : filling.NewEdge := ⟨leftEdge, by simp [filling]⟩
  let f : filling.NewEdge := ⟨rightEdge, by simp [filling]⟩
  refine ⟨0, 2, (), e, f, rfl, rfl, ?_, ?_, ?_, rfl, rfl, ?_, ?_, no_filled_pair⟩
  · change True
    trivial
  · change True
    trivial
  · intro hef
    have hSets : leftEdge = rightEdge := congrArg Subtype.val hef
    have hZero : (0 : Fin 3) ∈ rightEdge := by
      rw [← hSets]
      simp [leftEdge]
    norm_num [rightEdge] at hZero
  · change (0 : Fin 3) ∈ leftEdge
    simp [leftEdge]
  · change (2 : Fin 3) ∈ rightEdge
    simp [rightEdge]

/-- The short-or-long conclusion is essential even for this finite path
filling with all its edges owned by one designated target. -/
theorem short_requires_long :
    old.LinearPretrain ∧ filled.LinearPretrain ∧
    old.ShortPiece (.inl ()) (.inl 0) (.inl 2) ∧
    ¬ filled.ShortPiece (.inl ()) (.inl 0) (.inl 2) ∧
    filled.LongPiece (.inl ()) (.inl 0) (.inl 2) :=
  ⟨old_linearPretrain, filled_linearPretrain, old_short, no_filled_short, filled_long⟩

end StructuralRamsey.Girth.TrainFillingPieceLiftRegression
