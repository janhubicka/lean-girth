import Girth.ContactActualPictureStep

/-! The finite colour-focusing argument, independently of the
existence of each train witness. Every step retains an actual
standard edge injection and lifts all designated labels. The
reverse choice through a finite chain therefore returns an
actual designated copy of the final picture. -/

namespace StructuralRamsey.Girth
universe v

structure ContactFocusPicture (A B : Type v) where
  Edge : Type v
  Copy : Type v
  projection : Edge → B
  copy : Copy → A → Edge

namespace ContactFocusPicture
variable {A B Color : Type v}

/-- A single partite step, with actual edge and copy maps for the
standard selected by a colouring. -/
def Step (P Q : ContactFocusPicture A B) (b : B) (Color : Type v) : Prop :=
  ∀ χ : Q.Edge → Color, ∃ f : P.Edge ↪ Q.Edge, ∃ lift : P.Copy → Q.Copy,
    (∀ e, Q.projection (f e) = P.projection e) ∧
    (∀ i e, Q.copy (lift i) e = f (P.copy i e)) ∧
    ∃ c : Color, ∀ e, P.projection e = b → χ (f e) = c

/-- A chain is recorded in reverse step order. It is a finite
inductive object, not a hypothesis of a final Ramsey arrow. -/
inductive Chain (Color : Type v) :
    ContactFocusPicture A B → ContactFocusPicture A B → List B → Prop
  | nil (P : ContactFocusPicture A B) : Chain Color P P []
  | snoc {P Q R : ContactFocusPicture A B} {l : List B} {b : B} :
      Chain Color P Q l → Step Q R b Color → Chain Color P R (b :: l)

/-- Reverse colour focusing through the finite chain. The final
copy map lifts the actual initial designated labels. -/
theorem Chain.focus {P Q : ContactFocusPicture A B} {l : List B}
    (H : Chain Color P Q l) (χ : Q.Edge → Color) :
    ∃ f : P.Edge ↪ Q.Edge, ∃ lift : P.Copy → Q.Copy,
      (∀ e, Q.projection (f e) = P.projection e) ∧
      (∀ i e, Q.copy (lift i) e = f (P.copy i e)) ∧
      (∀ b ∈ l, ∃ c : Color, ∀ e, P.projection e = b → χ (f e) = c) := by
  induction H with
  | nil =>
    exact ⟨Function.Embedding.refl _,id,fun _ => rfl,fun _ _ => rfl,
      fun b hb => (by simpa using hb : False).elim⟩
  | @snoc Q R l b H hstep ih =>
    obtain ⟨g,k,hg,hk,c,hc⟩ := hstep χ
    obtain ⟨f,j,hf,hj,hm⟩ := ih (fun e => χ (g e))
    refine ⟨f.trans g,k ∘ j,?_,?_,?_⟩
    · intro e
      exact (hg (f e)).trans (hf e)
    · intro i e
      exact (hk (j i) e).trans (congrArg g (hj i e))
    · intro a ha
      rcases List.mem_cons.mp ha with he | he
      · subst a
        exact ⟨c,fun e he => hc (f e) ((hf e).trans he)⟩
      · exact hm a he

/-- When every base edge has been processed, the initial copy
colours factor through a single colouring of the base. Applying
the base arrow selects a designated label of the final picture. -/
theorem Chain.arrow_of_base [Nonempty Color]
    {P Q : ContactFocusPicture A B} {l : List B}
    (H : Chain Color P Q l) (hall : ∀ b : B, b ∈ l)
    (hbase : ∀ ρ : B → Color, ∃ i : P.Copy, ∃ c : Color,
      ∀ a : A, ρ (P.projection (P.copy i a)) = c) :
    ∀ χ : Q.Edge → Color, ∃ j : Q.Copy, ∃ c : Color,
      ∀ a : A, χ (Q.copy j a) = c := by
  classical
  intro χ
  obtain ⟨f,lift,_,hlift,hm⟩ := H.focus χ
  have h : ∀ b : B, ∃ c : Color, ∀ e : P.Edge,
      P.projection e = b → χ (f e) = c :=
    fun b => hm b (hall b)
  choose ρ hρ using h
  obtain ⟨i,c,hc⟩ := hbase ρ
  refine ⟨lift i,c,?_⟩
  intro a
  rw [hlift]
  exact (hρ (P.projection (P.copy i a)) (P.copy i a) rfl).trans (hc a)

end ContactFocusPicture

namespace ContactDesignatedEmbeddings
variable {V E I U F J X B W G K : Type v}
    {m : ℕ} {L : ContactHypergraphData V E I} {S : ContactTrainData E m}
    {base : B → Set X} {P : ContactBaseProjection L base} {b : B}
    {D : ContactHypergraphData U F J} {T : ContactTrainData F m}
    (M : ContactDesignatedEmbeddings (P.stripHypergraph b) (P.stripTrain S b) D T)
    {H : ContactHypergraphData W G K} {R : ContactTrainData G m}
    (N : ContactDesignatedEmbeddings H R L S)

def focusOld (P : ContactBaseProjection L base) : ContactFocusPicture G B where
  Edge := E
  Copy := I
  projection := P.edge
  copy := fun i e => (N.emb i).edge e

noncomputable def focusNew (hne : Nonempty (P.StripEdge b)) : ContactFocusPicture G B where
  Edge := (M.stripGluing hne).Edge
  Copy := J × I
  projection := (M.stripGluing hne).outputProjectionEdge P b
  copy := fun p e => (M.stripGluing hne).stdE p.1 ((N.emb p.2).edge e)

/-- The actual gluing supplies the step of the finite focusing
chain. For an empty strip no change is necessary; that case can
be handled by an identity step with any colour. -/
theorem focusStep {Color : Type v} (hne : Nonempty (P.StripEdge b))
    (h : M.Arrow Color) :
    ContactFocusPicture.Step (N.focusOld P) (M.focusNew N hne) b Color := by
  intro χ
  let A := M.stripGluing hne
  let hA := M.stripGluing_active hne
  obtain ⟨i,c,hi⟩ := M.strip_step_arrow hne h χ
  refine ⟨A.stdE i,fun j => (i,j),?_,?_,c,?_⟩
  · intro e
    exact A.projection_edge_std P b hA i e
  · intro j e
    rfl
  · intro e he
    exact hi ⟨e,he⟩

end ContactDesignatedEmbeddings
end StructuralRamsey.Girth
