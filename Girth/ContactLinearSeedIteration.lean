import Girth.ContactRawSeed
import Girth.ContactFocusingChain
import Girth.ContactGluedOrder

/-! Actual finite nonlinear seed iteration.

The target embeddings are retained externally while the old
picture has no designated copy labels. This avoids assuming that
the initial raw seed is induced or linear. Every new picture is
the tagged free union with the word-base core, and its linearity
and strong target embeddings follow from picture lemma (b). -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B : Type v}

/-- A height-one picture over a possibly nonlinear fixed base,
with actual strong embeddings of the original target. -/
structure ContactSeedStage (D : ContactHypergraphData V E I) (base : B → Set X) where
  Vertex : Type v
  Edge : Type v
  Copy : Type v
  finiteV : Finite Vertex
  finiteE : Finite Edge
  finiteC : Finite Copy
  graph : ContactHypergraphData Vertex Edge PEmpty.{v+1}
  train : ContactTrainData Edge 1
  projection : ContactBaseProjection graph base
  emb : Copy → ContactTrainEmbedding D (contactHeightOne E) graph train
  linear : ∀ e f : Edge, e ≠ f → (graph.edgeCarrier e ∩ graph.edgeCarrier f).Subsingleton

namespace ContactSeedStage
variable {D : ContactHypergraphData V E I} {base : B → Set X}
    (P : ContactSeedStage D base)

def focus : ContactFocusPicture E B where
  Edge := P.Edge
  Copy := P.Copy
  projection := P.projection.edge
  copy := fun i e => (P.emb i).edge e

theorem height_one_rel (T : ContactTrainData E 1) (μ : Fin 2) (e f : E) :
    T.parent μ e = T.parent μ f ↔ μ.val = 1 ∨ e = f := by
  constructor
  · intro h
    by_cases ht : μ.val = 1
    · exact Or.inl ht
    · have hz : μ = 0 := Fin.ext (by have := μ.isLt; omega)
      subst μ
      exact Or.inr (T.bottom h)
  · rintro (ht | rfl)
    · have ht' : μ = (⟨1,by omega⟩ : Fin 2) := Fin.ext ht
      rw [ht']
      exact T.top e f
    · rfl

/-- Retaining the exact height-one equivalences does not require
a new quotient identification for the word core. -/
noncomputable def wordCoreFamily (b : B) (N : Type) :
    ContactDesignatedEmbeddings
      (P.projection.stripHypergraph b) (P.projection.stripTrain P.train b)
      ((P.projection.stripEndpoints b).wordHypergraph N)
      (contactHeightOne (N → P.projection.StripEdge b)) where
  emb := fun l =>
    let M := (P.projection.stripEndpoints b).lineTrainEmbedding N
      (P.projection.strip_linear b P.linear) l
    { vertex := M.vertex
      edge := M.edge
      carrier_eq := M.carrier_eq
      rel_iff := fun μ e f =>
        (height_one_rel _ μ (M.edge e) (M.edge f)).trans
          ((or_congr Iff.rfl ⟨fun h => M.edge.injective h,fun h => congrArg M.edge h⟩).trans
            (height_one_rel _ μ e f).symm)
      strong := M.strong }
  vertex_eq := fun _ => rfl
  edge_eq := fun _ => rfl

/-- The actual projection of a word-core vertex onto the active
base edge. Its definition is independent of the chosen colouring. -/
noncomputable def wordCorePart (b : B) (N : Type)
    (x : (P.projection.stripEndpoints b).WordVertex N) : X :=
  ((P.projection.stripEndpoints b).wordPart N x).val

theorem wordCorePart_emb (b : B) (N : Type)
    (i : Combinatorics.Line (P.projection.StripEdge b) N)
    (x : P.projection.StripVertex b) :
    P.wordCorePart b N (((P.wordCoreFamily b N).emb i).vertex x) =
      P.projection.stripPart b x := rfl

theorem wordCorePart_image (b : B) (N : Type)
    (e : N → P.projection.StripEdge b) :
    P.wordCorePart b N '' ((P.projection.stripEndpoints b).wordHypergraph N).edgeCarrier e =
      base b := by
  let Q := P.projection.stripEndpoints b
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (Q.wordPart N y).property
  · intro hx
    let a : base b := ⟨x,hx⟩
    exact ⟨Q.wordEnd N e a,⟨a,rfl⟩,rfl⟩

theorem wordCorePart_inj (b : B) (N : Type)
    (e : N → P.projection.StripEdge b) :
    Set.InjOn (P.wordCorePart b N)
      (((P.projection.stripEndpoints b).wordHypergraph N).edgeCarrier e) := by
  let Q := P.projection.stripEndpoints b
  intro x hx y hy he
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨c,rfl⟩ := hy
  change a.val = c.val at he
  exact congrArg (Q.wordEnd N e) (Subtype.ext he)

noncomputable def wordGluing (b : B) (N : Type)
    (hne : Nonempty (P.projection.StripEdge b)) :=
  (P.wordCoreFamily b N).stripGluing hne

theorem wordGluing_coreOver (b : B) (N : Type)
    (hne : Nonempty (P.projection.StripEdge b)) :
    (P.wordGluing b N hne).CoreOver P.projection b (P.wordCorePart b N) :=
  (P.wordCoreFamily b N).stripGluing_coreOver hne (P.wordCorePart b N)
    (P.wordCorePart_emb b N) (P.wordCorePart_image b N) (P.wordCorePart_inj b N)

/-- Construct the entire next seed stage using an actual finite
word core. This construction is independent of a colouring;
the arrow hypothesis only determines which standard to select. -/
noncomputable def next (b : B) (N : Type) [Fintype N]
    (hne : Nonempty (P.projection.StripEdge b)) :
    ContactSeedStage D base := by
  letI : Finite P.Vertex := P.finiteV
  letI : Finite P.Edge := P.finiteE
  letI : Finite P.Copy := P.finiteC
  let Q := P.projection.stripEndpoints b
  let M := P.wordCoreFamily b N
  let A := P.wordGluing b N hne
  let p := P.wordCorePart b N
  let hA := M.stripGluing_active hne
  let hc := P.wordGluing_coreOver b N hne
  have hpair : A.TwoPartIntersection p := by
    intro i j hij u v hui huj hvi hvj huv
    exact Q.word_pair_geometry N (P.projection.strip_linear b P.linear)
      i j hij u v ⟨hui,huj⟩ ⟨hvi,hvj⟩ (fun he => huv (congrArg Subtype.val he))
  have hs := A.nonlinear_standard_strong P.projection b p hc hpair M.copy_strong P.linear
  have hlin := A.nonlinear_output_linear hs M.copy_strong
    (Q.word_linear N (P.projection.strip_linear b P.linear)) P.linear
  let hstd : ∀ i, ContactTrainEmbedding P.graph P.train
      A.outputHypergraph A.outputTrain := by
    intro i
    refine {
      vertex := A.stdV i
      edge := A.stdE i
      carrier_eq := fun e => A.output_carrier_std i (Sum.inr e)
      rel_iff := fun μ e f => A.outputTrain_std_rel μ i e f
      strong := ?_ }
    intro e he
    have hh : (A.bottomPicture.output.edgeCarrier e ∩ Set.range (A.stdV i)).Nontrivial := by
      rw [A.bottomPicture_output_eq]
      exact he
    exact hs i e hh
  let P' := A.outputProjection P.projection b p hA hc
  letI : Finite (Combinatorics.Line (P.projection.StripEdge b) N) :=
    Finite.of_injective (fun l => l.idxFun) (fun _ _ h => Combinatorics.Line.ext h)
  letI : Finite (base b) := Finite.of_injective
    (Q.endpoint (Classical.choice hne)) (Q.endpoint_inj _)
  letI : Finite (Q.WordVertex N) :=
    Finite.of_injective (fun x : Q.WordVertex N => (x.val : (base b) × (N → P.projection.StripVertex b))) Subtype.val_injective
  letI : Finite A.Vertex :=
    Finite.of_injective (fun x : A.Vertex => (x.val : Q.WordVertex N ⊕ (Combinatorics.Line (P.projection.StripEdge b) N × P.Vertex))) Subtype.val_injective
  letI : Finite A.Edge :=
    Finite.of_injective (fun x : A.Edge => (x.val : (N → P.projection.StripEdge b) ⊕ (Combinatorics.Line (P.projection.StripEdge b) N × P.Edge))) Subtype.val_injective
  exact {
    Vertex := A.Vertex
    Edge := A.Edge
    Copy := Combinatorics.Line (P.projection.StripEdge b) N × P.Copy
    finiteV := inferInstance
    finiteE := inferInstance
    finiteC := inferInstance
    graph := A.outputHypergraph.noCopies
    train := A.outputTrain
    projection := P'.noCopies
    emb := fun i => ((P.emb i.2).comp (hstd i.1)).noTargetCopies
    linear := hlin }

/-- The new designated embeddings keep the projected vertex map
of the old target embedding. This is the predicate preservation
needed to recover the original f-partite label word. -/
theorem next_emb_vertex (b : B) (N : Type) [Fintype N]
    (hne : Nonempty (P.projection.StripEdge b))
    (i : Combinatorics.Line (P.projection.StripEdge b) N) (j : P.Copy) (x : V) :
    (P.next b N hne).projection.vertex (((P.next b N hne).emb (i,j)).vertex x) =
      P.projection.vertex ((P.emb j).vertex x) := by
  change (P.wordGluing b N hne).outputProjectionVertex P.projection (P.wordCorePart b N)
    ((P.wordGluing b N hne).stdV i ((P.emb j).vertex x)) = _
  exact (P.wordGluing b N hne).projection_vertex_std P.projection b (P.wordCorePart b N)
    (P.wordGluing_coreOver b N hne) i ((P.emb j).vertex x)

/-- The constructed nonlinear picture supplies one genuine
focusing step, using the same actual edge and copy maps. -/
theorem next_focus (b : B) (N : Type) [Fintype N]
    (hne : Nonempty (P.projection.StripEdge b)) {Color : Type v}
    (hword : (P.wordCoreFamily b N).Arrow Color) :
    ContactFocusPicture.Step P.focus (P.next b N hne).focus b Color := by
  intro χ
  let M := P.wordCoreFamily b N
  let A := M.stripGluing hne
  obtain ⟨i,c,hi⟩ := M.strip_step_arrow hne hword χ
  refine ⟨A.stdE i,fun j => (i,j),?_,?_,c,?_⟩
  · intro e
    exact A.projection_edge_std P.projection b (M.stripGluing_active hne) i e
  · intro j e
    rfl
  · intro e he
    exact hi ⟨e,he⟩

/-- Hales--Jewett provides a next stage for every nonempty strip.
The empty strip is the identity step. -/
theorem exists_next (b : B) {Color : Type v} [Finite Color] [Nonempty Color] :
    ∃ Q : ContactSeedStage D base,
      ContactFocusPicture.Step P.focus Q.focus b Color := by
  classical
  by_cases hne : Nonempty (P.projection.StripEdge b)
  · letI : Finite P.Edge := P.finiteE
    obtain ⟨N,hN,hword⟩ :=
      (P.projection.stripEndpoints b).exists_word_arrow (Color := Color)
    letI : Fintype N := hN
    refine ⟨P.next b N hne,P.next_focus b N hne ?_⟩
    intro χ
    exact hword χ
  · refine ⟨P,?_⟩
    intro χ
    refine ⟨Function.Embedding.refl _,id,fun _ => rfl,fun _ _ => rfl,
      Classical.choice (inferInstance : Nonempty Color),?_⟩
    intro e he
    exact (hne ⟨⟨e,he⟩⟩).elim

/-- Construct the actual chain for any finite list of base edges.
No one-step existence hypothesis survives: the steps are the
Hales--Jewett tagged pictures above. -/
theorem exists_chain (l : List B) {Color : Type v} [Finite Color] [Nonempty Color] :
    ∃ Q : ContactSeedStage D base, ContactFocusPicture.Chain Color P.focus Q.focus l := by
  induction l with
  | nil => exact ⟨P,ContactFocusPicture.Chain.nil _⟩
  | cons b l ih =>
    obtain ⟨Q,hQ⟩ := ih
    obtain ⟨R,hR⟩ := Q.exists_next b (Color := Color)
    exact ⟨R,ContactFocusPicture.Chain.snoc hQ hR⟩

/-- Linear seed from the finite raw seed arrow. The result
retains actual strongly induced vertex and edge embeddings,
not just a family of vertex sets. -/
theorem exists_linear_seed [Fintype B] {Color : Type v} [Finite Color] [Nonempty Color]
    (hbase : ∀ ρ : B → Color, ∃ i : P.Copy, ∃ c : Color,
      ∀ e, ρ (P.projection.edge ((P.emb i).edge e)) = c) :
    ∃ Q : ContactSeedStage D base,
      ∀ χ : Q.Edge → Color, ∃ i : Q.Copy, ∃ c : Color,
        ∀ e, χ ((Q.emb i).edge e) = c := by
  classical
  let l := (Finset.univ : Finset B).toList
  obtain ⟨Q,hQ⟩ := P.exists_chain l (Color := Color)
  refine ⟨Q,hQ.arrow_of_base ?_ hbase⟩
  intro b
  simp [l]

end ContactSeedStage

namespace ContactOrderedEdgeWord
variable {D : ContactHypergraphData V E I} {P : Type v} [LinearOrder V]
    {a : ℕ} (A : ContactOrderedEdgeWord D P a)

noncomputable def rawStage (N : ℕ) [Finite V] [Finite E] [Finite P]
    (hinj : Function.Injective (fun e : E => D.edgeCarrier e))
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    ContactSeedStage D (A.seedCarrier N) := by
  letI : Finite (V ↪o Fin N) := contactFiniteOrderEmbedding V (Fin N)
  exact {
  Vertex := (V ↪o Fin N) × V
  Edge := (V ↪o Fin N) × E
  Copy := V ↪o Fin N
  finiteV := inferInstance
  finiteE := inferInstance
  finiteC := inferInstance
  graph := (D.disjointCopies (V ↪o Fin N)).noCopies
  train := contactHeightOne _
  projection := A.rawInitialProjection N hinj
  emb := fun j => {
    vertex := ⟨Prod.mk j,fun _ _ he => congrArg Prod.snd he⟩
    edge := ⟨Prod.mk j,fun _ _ he => congrArg Prod.snd he⟩
    carrier_eq := by
      intro e
      ext x
      constructor
      · rintro ⟨hx₁,hx₂⟩
        exact ⟨x.2,hx₂,Prod.ext hx₁.symm rfl⟩
      · rintro ⟨x,hx,rfl⟩
        exact ⟨rfl,hx⟩
    rel_iff := contactHeightOne_embedding_rel ⟨Prod.mk j,fun _ _ he => congrArg Prod.snd he⟩
    strong := by
      rintro ⟨k,e⟩ hn
      obtain ⟨x,hx,_,_,_⟩ := hn
      obtain ⟨y,hy⟩ := hx.2
      have he : j = k := (congrArg Prod.fst hy).trans hx.1.1
      subst k
      exact ⟨e,rfl⟩ }
  linear := rawInitial_linear (D := D) N hlin }

/-- Complete elementary linear-seed existence on actual labelled
hypergraphs, using finite Ramsey followed by nonlinear-base
word steps. The within-part order construction is a separate
adapter; this result concerns the carrier geometry and arrow. -/
theorem exists_unordered_linear_seed [Fintype V] [Finite E] [Finite P]
    {Color : Type v} [Fintype Color] [Nonempty Color] [Nonempty E]
    (hinj : Function.Injective (fun e : E => D.edgeCarrier e))
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    ∃ N : ℕ, ∃ Q : ContactSeedStage D (A.seedCarrier N),
      ∀ χ : Q.Edge → Color, ∃ i : Q.Copy, ∃ c : Color,
        ∀ e, χ ((Q.emb i).edge e) = c := by
  classical
  obtain ⟨N,hN⟩ := A.exists_raw_seed_arrow (Color := Color) hinj
  letI : Finite (A.SeedEdge N) := A.seedEdgeFinite N
  letI : Fintype (A.SeedEdge N) := Fintype.ofFinite _
  obtain ⟨Q,hQ⟩ := (A.rawStage N hinj hlin).exists_linear_seed (Color := Color) hN
  exact ⟨N,Q,hQ⟩

end ContactOrderedEdgeWord
end StructuralRamsey.Girth
