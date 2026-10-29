import Girth.TrainRecursiveWitnessPass
import Girth.InitialACopyGeometry

/-!
# Actual initial physical support and selected train copies

The initial picture contains a literal disjoint B-copy for each prescribed
base label.  Every ambient A-edge is retained: irreducibility places it in
one component, and nonemptiness of A makes that physical component unique.
This identifies the actual support edge type with component × target edge.

The train below is built on that complete physical edge type.  At every
proper cut it is the disjoint union of the target train relations, and the
universal top joins the components.  Its restriction to each literal
selected target copy preserves and reflects every target train level.

The no-isolated-vertices and nonempty-support conclusions have explicit
corresponding target hypotheses.  Initial mixed bottom forest bounds,
adjacent parameters, tail system-girth, and remaining-fibre refinability
are not inferred from this physical support construction.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P I : Type v}

/-- The component train is a disjoint union below its universal top. -/
def componentTrain {E : Type v} {m : ℕ}
    (T : EdgeTrainLevels E m) (hm : 0 < m) :
    EdgeTrainLevels (I × E) m where
  rel μ a b := μ.val = m ∨ (a.1 = b.1 ∧ T.rel μ a.2 b.2)
  equivalent := by
    intro μ
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact Or.inr ⟨rfl, (T.equivalent μ).refl a.2⟩
    · intro a b h
      rcases h with h | ⟨hab, hrel⟩
      · exact Or.inl h
      · exact Or.inr ⟨hab.symm, (T.equivalent μ).symm hrel⟩
    · intro a b c hab hbc
      rcases hab with h | ⟨hi, hrel⟩
      · exact Or.inl h
      rcases hbc with h | ⟨hj, hrel'⟩
      · exact Or.inl h
      · exact Or.inr ⟨hi.trans hj, (T.equivalent μ).trans hrel hrel'⟩
  nested := by
    intro μ ν hμν a b h
    rcases h with htop | ⟨hi, hrel⟩
    · left
      have hν := ν.isLt
      change μ.val ≤ ν.val at hμν
      omega
    · exact Or.inr ⟨hi, T.nested μ ν hμν a.2 b.2 hrel⟩
  bottom := by
    intro a b
    constructor
    · rintro (htop | ⟨hi, hrel⟩)
      · exact (Nat.ne_of_gt hm htop.symm).elim
      · exact Prod.ext hi ((T.bottom a.2 b.2).mp hrel)
    · intro h
      subst b
      exact Or.inr ⟨rfl, (T.bottom a.2 a.2).mpr rfl⟩
  top := fun _ _ => Or.inl rfl

/-- The top merge never changes the original relations inside one component. -/
theorem componentTrain_same_component_iff {E : Type v} {m : ℕ}
    (T : EdgeTrainLevels E m) (hm : 0 < m) (i : I)
    (μ : Fin (m + 1)) (e f : E) :
    (componentTrain T hm).rel μ (i, e) (i, f) ↔ T.rel μ e f := by
  constructor
  · rintro (htop | ⟨_, hrel⟩)
    · have hμ : μ = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext htop
      subst μ
      exact T.top e f
    · exact hrel
  · intro hrel
    exact Or.inr ⟨rfl, hrel⟩

/-- The physical image of one target support edge in one initial component. -/
def initialPhysicalEdge
    (A : RelStructure L UA) (B : RelStructure L VB) (β : I → VB ↪ P)
    (p : I × OldACarrierEdge A B) :
    OldACarrierEdge A (StructuralRamsey.Partite.Initial.picture B β).toRelStructure :=
  ⟨(fun b : VB => (p.1, b)) '' p.2.1, by
    rcases p.2.2 with ⟨a, ha⟩
    refine ⟨(StructuralRamsey.Partite.Initial.copyEmbedding B β p.1).comp a, ?_⟩
    rw [ha]
    exact (copyCarrier_comp_eq_image
      (StructuralRamsey.Partite.Initial.copyEmbedding B β p.1) a).symm⟩

/-- This physical map agrees with composition of actual embeddings. -/
theorem initialPhysicalEdge_actualEdge
    (A : RelStructure L UA) (B : RelStructure L VB) (β : I → VB ↪ P)
    (i : I) (a : RelStructure.Embedding A B) :
    initialPhysicalEdge A B β (i, actualEdge a) =
      actualEdge ((StructuralRamsey.Partite.Initial.copyEmbedding B β i).comp a) := by
  apply Subtype.ext
  exact (copyCarrier_comp_eq_image
    (StructuralRamsey.Partite.Initial.copyEmbedding B β i) a).symm

/-- Nonempty physical A-edges in disjoint components cannot be identified. -/
theorem initialPhysicalEdge_injective
    (A : RelStructure L UA) [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) :
    Function.Injective (initialPhysicalEdge A B β) := by
  classical
  rintro ⟨i, e⟩ ⟨j, f⟩ h
  have hcar := congrArg Subtype.val h
  change (fun b : VB => (i, b)) '' e.1 =
    (fun b : VB => (j, b)) '' f.1 at hcar
  have hne : e.1.Nonempty := by
    rcases e.2 with ⟨a, ha⟩
    obtain ⟨u⟩ := (inferInstance : Nonempty UA)
    exact ⟨a u, by rw [ha]; exact ⟨u, rfl⟩⟩
  obtain ⟨b, hb⟩ := hne
  have hmem : (i, b) ∈ (fun c : VB => (j, c)) '' f.1 :=
    hcar ▸ ⟨b, hb, rfl⟩
  obtain ⟨c, _, hc⟩ := hmem
  have hij : i = j := (congrArg Prod.fst hc).symm
  subst j
  congr 1
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    have hx' : (i, x) ∈ (fun b : VB => (i, b)) '' f.1 :=
      hcar ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hx'
    have hxy' : y = x := congrArg Prod.snd hxy
    exact hxy' ▸ hy
  · intro hx
    have hx' : (i, x) ∈ (fun b : VB => (i, b)) '' e.1 :=
      hcar.symm ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hx'
    have hxy' : y = x := congrArg Prod.snd hxy
    exact hxy' ▸ hy

/-- Every actual ambient A-edge occurs, by irreducible component factoring. -/
theorem initialPhysicalEdge_surjective
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I] :
    Function.Surjective (initialPhysicalEdge A B β) := by
  intro e
  rcases e.2 with ⟨a, ha⟩
  obtain ⟨i, b, hb⟩ := initialACopy_factors_component A hA B β a
  refine ⟨(i, actualEdge b), ?_⟩
  rw [initialPhysicalEdge_actualEdge]
  apply Subtype.ext
  exact (ha.trans (congrArg copyCarrier hb)).symm

/-- Exact physical edge enumeration; it retains all ambient initial edges. -/
noncomputable def initialPhysicalEdgeEquiv
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I] :
    (I × OldACarrierEdge A B) ≃
      OldACarrierEdge A
        (StructuralRamsey.Partite.Initial.picture B β).toRelStructure :=
  Equiv.ofBijective (initialPhysicalEdge A B β)
    ⟨initialPhysicalEdge_injective A B β,
      initialPhysicalEdge_surjective A hA B β⟩

/-- The actual initial train on the complete physical support edge type. -/
noncomputable def initialTrain
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m) :
    EdgeTrainLevels (OldACarrierEdge A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure) m :=
  (componentTrain (I := I) T hm).restrict
    (initialPhysicalEdgeEquiv A hA B β).symm.toEmbedding

/-- Every actual component is a train embedding, with reflection at all cuts. -/
theorem initialTrain_component_iff
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
    (i : I) (μ : Fin (m + 1)) (e f : OldACarrierEdge A B) :
    (initialTrain A hA B β T hm).rel μ
      (initialPhysicalEdge A B β (i, e))
      (initialPhysicalEdge A B β (i, f)) ↔ T.rel μ e f := by
  change (componentTrain T hm).rel μ
    ((initialPhysicalEdgeEquiv A hA B β).symm
      ((initialPhysicalEdgeEquiv A hA B β) (i, e)))
    ((initialPhysicalEdgeEquiv A hA B β).symm
      ((initialPhysicalEdgeEquiv A hA B β) (i, f))) ↔ _
  simp only [Equiv.symm_apply_apply]
  exact componentTrain_same_component_iff T hm i μ e f

/-- The restriction law in the exact embedding form required by a pass stage. -/
theorem initialTrain_targetRestriction
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
    (i : I) (μ : Fin (m + 1)) (a₁ a₂ : RelStructure.Embedding A B) :
    (initialTrain A hA B β T hm).rel μ
      (actualEdge ((StructuralRamsey.Partite.Initial.copyEmbedding B β i).comp a₁))
      (actualEdge ((StructuralRamsey.Partite.Initial.copyEmbedding B β i).comp a₂)) ↔
      T.rel μ (actualEdge a₁) (actualEdge a₂) := by
  rw [← initialPhysicalEdge_actualEdge, ← initialPhysicalEdge_actualEdge]
  exact initialTrain_component_iff A hA B β T hm i μ _ _

/-- An actual component is A-strong because irreducible A-copies stay inside
one component.  This proof uses the complete initial support. -/
theorem initialComponent_aStrong
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I] (i : I) :
    AStrong A (StructuralRamsey.Partite.Initial.picture B β).toRelStructure
      (copyCarrier (StructuralRamsey.Partite.Initial.copyEmbedding B β i)) := by
  intro a hmeet
  obtain ⟨j, b, rfl⟩ := initialACopy_factors_component A hA B β a
  by_cases hji : j = i
  · subst j
    rintro x ⟨u, hu⟩
    exact ⟨b u, hu⟩
  · exfalso
    apply hmeet
    intro x hx y hy
    obtain ⟨u, hu⟩ := hx.1
    obtain ⟨v, hv⟩ := hx.2
    exact (hji (congrArg Prod.fst (hu.trans hv.symm))).elim

/-- Target support coverage supplies coverage of every initial vertex. -/
theorem initial_supportCovers
    (A : RelStructure L UA) (B : RelStructure L VB) (β : I → VB ↪ P)
    (hCover : ∀ b : VB, ∃ e : OldACarrierEdge A B, b ∈ e.1) :
    ∀ x : I × VB, ∃ e : OldACarrierEdge A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure, x ∈ e.1 := by
  rintro ⟨i, b⟩
  obtain ⟨e, he⟩ := hCover b
  exact ⟨initialPhysicalEdge A B β (i, e), ⟨b, he, rfl⟩⟩

/-- Nonempty support is carried from an explicit target support hypothesis. -/
theorem initial_supportNonempty
    (A : RelStructure L UA) (B : RelStructure L VB) (β : I → VB ↪ P)
    [Nonempty I] (hEdge : Nonempty (OldACarrierEdge A B)) :
    Nonempty (OldACarrierEdge A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  obtain ⟨e⟩ := hEdge
  exact ⟨initialPhysicalEdge A B β (i, e)⟩

/-- Every initial projection fibre is a matching of actual A-copy carriers.
Within one component, the injective base projection determines its embedding;
different components have disjoint carriers.  This supplies the physical
matching fact used to initialize remaining-fibre refinability.
-/
theorem initialFibre_pairwiseDisjoint
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]
    (α : UA ↪ P)
    (e f : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Initial.picture B β) α)
    (hne : e ≠ f) : Disjoint (copyCarrier e.val) (copyCarrier f.val) := by
  rw [Set.disjoint_left]
  intro x hx hy
  obtain ⟨i, a, he⟩ := initialACopy_factors_component A hA B β e.val
  obtain ⟨j, b, hf⟩ := initialACopy_factors_component A hA B β f.val
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  have hpoint :
      (StructuralRamsey.Partite.Initial.copyEmbedding B β i).comp a u =
        (StructuralRamsey.Partite.Initial.copyEmbedding B β j).comp b v := by
    rw [← he, ← hf]
    exact hu.trans hv.symm
  have hij : i = j := congrArg Prod.fst hpoint
  subst j
  apply hne
  apply Subtype.ext
  apply RelStructure.Embedding.ext
  intro w
  have hp := (e.property w).trans (f.property w).symm
  rw [he, hf] at hp
  rw [he, hf]
  exact Prod.ext rfl ((β i).injective hp)

section Selected

variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P) (family : Set (RelStructure.Embedding B D))

/-- The selected labels of the initial picture are precisely its literal
component copies, rather than all projected lifts. -/
def initialSelected := Set.range (initialDesignatedCopy B D family)

/-- Literal selected labels are physically distinct when B is nonempty. -/
theorem initialSelected_physical_injective [Nonempty VB] :
    Function.Injective (fun q :
      {q : DesignatedCopy B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding)) family //
        q ∈ initialSelected B D family} => bSupportPiece A q.1.embedding) := by
  rintro ⟨q, hq⟩ ⟨r, hr⟩ h
  apply Subtype.ext
  obtain ⟨b, rfl⟩ := hq
  obtain ⟨c, rfl⟩ := hr
  have hcar := congrArg HypergraphPiece.carrier h
  change copyCarrier (initialDesignatedCopy B D family b).embedding =
    copyCarrier (initialDesignatedCopy B D family c).embedding at hcar
  obtain ⟨v⟩ := (inferInstance : Nonempty VB)
  have hv : (b, v) ∈ copyCarrier (initialDesignatedCopy B D family c).embedding := by
    rw [← hcar]
    exact ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := hv
  have hbc : b = c := (congrArg Prod.fst hw).symm
  subst c
  rfl

/-- Every initial irreducible is covered by one of the literal selected
copies; no unselected designated lift is used. -/
theorem initialSelected_mixedCoverage [Nonempty family] :
    ∀ S : Set (family × VB),
      ((StructuralRamsey.Partite.Initial.picture B
        (fun b : family => b.1.toFunctionEmbedding)).toRelStructure.induce S).Irreducible →
      ∃ q : DesignatedCopy B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding)) family,
        q ∈ initialSelected B D family ∧
        ∀ z : S, ∃ b : VB, z.1 = q.embedding b := by
  intro S hS
  obtain ⟨i, hi⟩ := StructuralRamsey.Partite.Induced.Initial.irreducible_same_index
    B (fun b : family => b.1.toFunctionEmbedding) S hS
  refine ⟨initialDesignatedCopy B D family i, ⟨i, rfl⟩, ?_⟩
  intro z
  exact ⟨z.1.2, Prod.ext (hi z) rfl⟩

/-- Selected initial target copies are A-strong in the actual whole picture. -/
theorem initialSelected_strong (hA : A.Irreducible) [Nonempty family]
    (q : DesignatedCopy B D
      (StructuralRamsey.Partite.Initial.picture B
        (fun b : family => b.1.toFunctionEmbedding)) family)
    (hq : q ∈ initialSelected B D family) :
    AStrong A (StructuralRamsey.Partite.Initial.picture B
      (fun b : family => b.1.toFunctionEmbedding)).toRelStructure
      (copyCarrier q.embedding) := by
  obtain ⟨b, rfl⟩ := hq
  exact initialComponent_aStrong A hA B
    (fun b : family => b.1.toFunctionEmbedding) b

/-- Exact target-train restriction for each literal selected initial copy. -/
theorem initialSelected_targetRestriction
    (hA : A.Irreducible) [Nonempty UA] [Nonempty family]
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
    (q : DesignatedCopy B D
      (StructuralRamsey.Partite.Initial.picture B
        (fun b : family => b.1.toFunctionEmbedding)) family)
    (hq : q ∈ initialSelected B D family)
    (μ : Fin (m + 1)) (a₁ a₂ : RelStructure.Embedding A B) :
    (initialTrain A hA B (fun b : family => b.1.toFunctionEmbedding) T hm).rel μ
      (actualEdge (q.embedding.comp a₁)) (actualEdge (q.embedding.comp a₂)) ↔
      T.rel μ (actualEdge a₁) (actualEdge a₂) := by
  obtain ⟨b, rfl⟩ := hq
  exact initialTrain_targetRestriction A hA B
    (fun b : family => b.1.toFunctionEmbedding) T hm b μ a₁ a₂

end Selected

end StructuralRamsey.Girth.TrainRecursiveWitness
