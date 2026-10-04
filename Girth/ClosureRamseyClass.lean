import Girth.ElementaryClosureAmalgam
import PartiteConstruction.Ramsey.FreeAmalgamationFunctions

/-! # The elementary closure class and functional EHN

The class used in the A-linear Ramsey input consists of structures in the
c_A/c_B language whose relational reduct is A-linear and whose c_A fibre has
the prescribed pair-closure semantics.  The c_B fibre is deliberately
unrestricted.  This is the exact class to which the functional EHN theorem is
applied.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X Y : Type v}

/-- Forget the closure functions from a full embedding. -/
def closureEmbeddingRel
    {C : Structure (closureLanguage L) V}
    {D : Structure (closureLanguage L) W}
    (e : Structure.Embedding C D) :
    RelStructure.Embedding (closureRelReduct C) (closureRelReduct D) where
  toFun := e
  injective := e.injective
  map_rel_iff R x := e.map_rel_iff R x

/-- Exact semantics of the elementary pair-closure function c_A. -/
def CACompatible
    (A : RelStructure L U)
    (C : Structure (closureLanguage L) V) : Prop :=
  ∀ x : Fin 2 → V,
    C.func .cA x = cAValue A (closureRelReduct C) x

/-- The hereditary free-amalgamation class used for functional EHN.
The c_B interpretation is arbitrary. -/
def ElementaryClosureClass
    (A : RelStructure L U) :
    Structure.StructureClass (L := closureLanguage L) :=
  fun C =>
    ALinear A (closureRelReduct C) ∧ CACompatible A C

/-- The closure language has positive function arities. -/
theorem closureLanguage_positiveFuncArity :
    (closureLanguage L).PositiveFuncArity := by
  intro F
  cases F <;> simp [closureLanguage]

/-- The canonical elementary expansion belongs to the semantic closure class. -/
theorem elementaryClosureExpansion_mem
    {A : RelStructure L U} {D : RelStructure L V}
    (hD : ALinear A D) :
    ElementaryClosureClass A (elementaryClosureExpansion A D) := by
  refine ⟨hD, ?_⟩
  intro x
  rfl

/-- The target expansion also belongs: c_B is unrestricted by the class. -/
theorem targetClosureExpansion_mem
    {A : RelStructure L U} {B : RelStructure L V}
    (hB : ALinear A B) :
    ElementaryClosureClass A (targetClosureExpansion A B) := by
  refine ⟨hB, ?_⟩
  intro x
  rfl

/-- A full free amalgam in the closure language is in particular a relational
free amalgam after forgetting c_A and c_B. -/
theorem structureFreeAmalgam_relReduct
    {Base : Structure (closureLanguage L) U}
    {Left : Structure (closureLanguage L) V}
    {Right : Structure (closureLanguage L) W}
    {Whole : Structure (closureLanguage L) X}
    {fL : Structure.Embedding Base Left}
    {fR : Structure.Embedding Base Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hfree : Structure.IsFreeAmalgam fL fR iL iR) :
    RelStructure.IsFreeAmalgam
      (closureEmbeddingRel fL) (closureEmbeddingRel fR)
      (closureEmbeddingRel iL) (closureEmbeddingRel iR) where
  covers := hfree.covers
  overlap := hfree.overlap
  rel_iff R z := by
    simpa [closureLanguage] using hfree.rel_iff R z

/-- In a structure with the correct c_A semantics, every function-closed set
is A-strong in the relational reduct. -/
theorem aStrong_of_isClosed_of_cACompatible
    {A : RelStructure L U}
    {C : Structure (closureLanguage L) V}
    (hCA : CACompatible A C)
    {S : Set V} (hClosed : C.IsClosed S) :
    AStrong A (closureRelReduct C) S := by
  intro a hMeet
  rw [Set.not_subsingleton_iff] at hMeet
  rcases hMeet with ⟨x, hx, y, hy, hxy⟩
  intro z hz
  let args : Fin 2 → V := ![x, y]
  have hzCA : z ∈ cAValue A (closureRelReduct C) args := by
    exact ⟨hxy, a, hx.1, hy.1, hz⟩
  have hzFunc : z ∈ C.func .cA args := by
    rw [hCA args]
    exact hzCA
  exact hClosed .cA args (by
    intro i
    fin_cases i
    · exact hx.2
    · exact hy.2) hzFunc

/-- Therefore the range of every full embedding into a compatible structure is
A-strong. -/
theorem closureEmbedding_range_aStrong
    {A : RelStructure L U}
    {C : Structure (closureLanguage L) V}
    {D : Structure (closureLanguage L) W}
    (hD : CACompatible A D)
    (e : Structure.Embedding C D) :
    AStrong A (closureRelReduct D) (Set.range e) :=
  aStrong_of_isClosed_of_cACompatible hD e.range_isClosed

/-- Exact c_A semantics pull back along a full embedding. -/
theorem cACompatible_of_embedding
    {A : RelStructure L U}
    {C : Structure (closureLanguage L) V}
    {D : Structure (closureLanguage L) W}
    (hD : CACompatible A D)
    (e : Structure.Embedding C D) :
    CACompatible A C := by
  intro x
  apply Set.ext
  intro y
  let er := closureEmbeddingRel e
  constructor
  · intro hy
    have hey : e y ∈ D.func .cA (e ∘ x) := by
      have h :
          e y ∈ Structure.imageSet e (C.func .cA x) :=
        ⟨y, hy, rfl⟩
      rw [e.map_func .cA x] at h
      exact h
    rw [hD (e ∘ x)] at hey
    rcases hey with ⟨hneq, b, h0, h1, hyb⟩
    have hRange : ∀ a : U, ∃ z : V, b a = er z := by
      intro a
      have haCA :
          b a ∈ cAValue A (closureRelReduct D) (e ∘ x) :=
        ⟨hneq, b, h0, h1, ⟨a, rfl⟩⟩
      rw [← hD (e ∘ x)] at haCA
      rw [← e.map_func .cA x] at haCA
      rcases haCA with ⟨z, _hz, hez⟩
      exact ⟨z, hez.symm⟩
    let bC : RelStructure.Embedding A (closureRelReduct C) :=
      b.factorThroughRange er hRange
    have hbC (a : U) : b a = er (bC a) :=
      Classical.choose_spec (hRange a)
    have hneqC : x 0 ≠ x 1 := by
      intro h
      apply hneq
      exact congrArg e h
    have h0C : x 0 ∈ copyCarrier bC := by
      rcases h0 with ⟨a0, ha0⟩
      refine ⟨a0, ?_⟩
      apply e.injective
      calc
        e (bC a0) = b a0 := (hbC a0).symm
        _ = e (x 0) := ha0
    have h1C : x 1 ∈ copyCarrier bC := by
      rcases h1 with ⟨a1, ha1⟩
      refine ⟨a1, ?_⟩
      apply e.injective
      calc
        e (bC a1) = b a1 := (hbC a1).symm
        _ = e (x 1) := ha1
    have hyC : y ∈ copyCarrier bC := by
      rcases hyb with ⟨ay, hay⟩
      refine ⟨ay, ?_⟩
      apply e.injective
      calc
        e (bC ay) = b ay := (hbC ay).symm
        _ = e y := hay
    exact ⟨hneqC, bC, h0C, h1C, hyC⟩
  · intro hy
    rcases hy with ⟨hneq, a, h0, h1, hya⟩
    have heyCA :
        e y ∈ cAValue A (closureRelReduct D) (e ∘ x) := by
      refine ⟨?_, er.comp a, ?_, ?_, ?_⟩
      · intro h
        exact hneq (e.injective h)
      · rcases h0 with ⟨u0, hu0⟩
        exact ⟨u0, congrArg e hu0⟩
      · rcases h1 with ⟨u1, hu1⟩
        exact ⟨u1, congrArg e hu1⟩
      · rcases hya with ⟨uy, huy⟩
        exact ⟨uy, congrArg e huy⟩
    rw [← hD (e ∘ x)] at heyCA
    rw [← e.map_func .cA x] at heyCA
    rcases heyCA with ⟨z, hz, hez⟩
    have hzy : z = y := e.injective hez
    simpa [hzy] using hz

/-- The prescribed c_A semantics are preserved by a full free amalgam. -/
theorem cACompatible_of_freeAmalgam
    {A : RelStructure L U}
    {Base : Structure (closureLanguage L) X}
    {Left : Structure (closureLanguage L) V}
    {Right : Structure (closureLanguage L) W}
    {Whole : Structure (closureLanguage L) Y}
    {fL : Structure.Embedding Base Left}
    {fR : Structure.Embedding Base Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hAirr : A.Irreducible)
    (hL : CACompatible A Left)
    (hR : CACompatible A Right)
    (hfree : Structure.IsFreeAmalgam fL fR iL iR) :
    CACompatible A Whole := by
  intro x
  apply Set.ext
  intro y
  let hfreeR := structureFreeAmalgam_relReduct hfree
  let iLr := closureEmbeddingRel iL
  let iRr := closureEmbeddingRel iR
  constructor
  · intro hy
    rcases (hfree.func_iff .cA x y).mp hy with
      ⟨args, b, hb, hx, hyb⟩ |
      ⟨args, b, hb, hx, hyb⟩
    · rw [hL args] at hb
      rcases hb with ⟨hneq, a, h0, h1, hb⟩
      refine ⟨?_, iLr.comp a, ?_, ?_, ?_⟩
      · intro h
        apply hneq
        apply iL.injective
        calc
          iL (args 0) = x 0 := (congrFun hx 0).symm
          _ = x 1 := h
          _ = iL (args 1) := congrFun hx 1
      · rcases h0 with ⟨u0, hu0⟩
        refine ⟨u0, ?_⟩
        calc
          iL (a u0) = iL (args 0) := congrArg iL hu0
          _ = x 0 := (congrFun hx 0).symm
      · rcases h1 with ⟨u1, hu1⟩
        refine ⟨u1, ?_⟩
        calc
          iL (a u1) = iL (args 1) := congrArg iL hu1
          _ = x 1 := (congrFun hx 1).symm
      · rcases hb with ⟨uy, huy⟩
        refine ⟨uy, ?_⟩
        calc
          iL (a uy) = iL b := congrArg iL huy
          _ = y := hyb.symm
    · rw [hR args] at hb
      rcases hb with ⟨hneq, a, h0, h1, hb⟩
      refine ⟨?_, iRr.comp a, ?_, ?_, ?_⟩
      · intro h
        apply hneq
        apply iR.injective
        calc
          iR (args 0) = x 0 := (congrFun hx 0).symm
          _ = x 1 := h
          _ = iR (args 1) := congrFun hx 1
      · rcases h0 with ⟨u0, hu0⟩
        refine ⟨u0, ?_⟩
        calc
          iR (a u0) = iR (args 0) := congrArg iR hu0
          _ = x 0 := (congrFun hx 0).symm
      · rcases h1 with ⟨u1, hu1⟩
        refine ⟨u1, ?_⟩
        calc
          iR (a u1) = iR (args 1) := congrArg iR hu1
          _ = x 1 := (congrFun hx 1).symm
      · rcases hb with ⟨uy, huy⟩
        refine ⟨uy, ?_⟩
        calc
          iR (a uy) = iR b := congrArg iR huy
          _ = y := hyb.symm
  · intro hy
    rcases hy with ⟨hneq, a, h0, h1, hya⟩
    rcases irreducibleCopy_side_of_freeAmalgam
        hfreeR hAirr a with
      ⟨aL, haL⟩ | ⟨aR, haR⟩
    · change copyCarrier a = copyCarrier (iLr.comp aL) at haL
      have h0' : x 0 ∈ copyCarrier (iLr.comp aL) := by
        rw [← haL]
        exact h0
      have h1' : x 1 ∈ copyCarrier (iLr.comp aL) := by
        rw [← haL]
        exact h1
      have hy' : y ∈ copyCarrier (iLr.comp aL) := by
        rw [← haL]
        exact hya
      rcases h0' with ⟨u0, hu0⟩
      rcases h1' with ⟨u1, hu1⟩
      rcases hy' with ⟨uy, huy⟩
      let args : Fin 2 → V := ![aL u0, aL u1]
      have hb : aL uy ∈ Left.func .cA args := by
        rw [hL args]
        refine ⟨?_, aL, ?_, ?_, ?_⟩
        · intro heq
          apply hneq
          calc
            x 0 = iL (aL u0) := hu0.symm
            _ = iL (aL u1) := congrArg iL heq
            _ = x 1 := hu1
        · exact ⟨u0, rfl⟩
        · exact ⟨u1, rfl⟩
        · exact ⟨uy, rfl⟩
      apply (hfree.func_iff .cA x y).mpr
      left
      refine ⟨args, aL uy, hb, ?_, ?_⟩
      · funext j
        fin_cases j
        · exact hu0.symm
        · exact hu1.symm
      · exact huy.symm
    · change copyCarrier a = copyCarrier (iRr.comp aR) at haR
      have h0' : x 0 ∈ copyCarrier (iRr.comp aR) := by
        rw [← haR]
        exact h0
      have h1' : x 1 ∈ copyCarrier (iRr.comp aR) := by
        rw [← haR]
        exact h1
      have hy' : y ∈ copyCarrier (iRr.comp aR) := by
        rw [← haR]
        exact hya
      rcases h0' with ⟨u0, hu0⟩
      rcases h1' with ⟨u1, hu1⟩
      rcases hy' with ⟨uy, huy⟩
      let args : Fin 2 → W := ![aR u0, aR u1]
      have hb : aR uy ∈ Right.func .cA args := by
        rw [hR args]
        refine ⟨?_, aR, ?_, ?_, ?_⟩
        · intro heq
          apply hneq
          calc
            x 0 = iR (aR u0) := hu0.symm
            _ = iR (aR u1) := congrArg iR heq
            _ = x 1 := hu1
        · exact ⟨u0, rfl⟩
        · exact ⟨u1, rfl⟩
        · exact ⟨uy, rfl⟩
      apply (hfree.func_iff .cA x y).mpr
      right
      refine ⟨args, aR uy, hb, ?_, ?_⟩
      · funext j
        fin_cases j
        · exact hu0.symm
        · exact hu1.symm
      · exact huy.symm

/-- The semantic elementary closure class is hereditary and closed under full
free amalgamation. -/
theorem elementaryClosureClass_freeAmalgamation
    {A : RelStructure L U}
    (hAirr : A.Irreducible) :
    Structure.FreeAmalgamationClass (ElementaryClosureClass A) := by
  constructor
  · intro Y Z C D hD e
    refine ⟨?_, ?_⟩
    · exact aLinear_of_embedding hD.1 (closureEmbeddingRel e)
    · exact cACompatible_of_embedding hD.2 e
  · intro H E F C Base Left Right Whole
      sL sR iL iR hL hR hfree
    let hfreeR := structureFreeAmalgam_relReduct hfree
    have hStrongL :
        AStrong A (closureRelReduct Left)
          (copyCarrier (closureEmbeddingRel sL)) :=
      closureEmbedding_range_aStrong hL.2 sL
    have hStrongR :
        AStrong A (closureRelReduct Right)
          (copyCarrier (closureEmbeddingRel sR)) :=
      closureEmbedding_range_aStrong hR.2 sR
    refine ⟨?_, ?_⟩
    · exact aLinear_of_freeAmalgam hAirr hL.1 hR.1
        hStrongL hStrongR hfreeR
    · exact cACompatible_of_freeAmalgam hAirr hL.2 hR.2 hfree

/-- Functional EHN specialized to the elementary A-closure class.
The c_B symbol remains unrestricted in the witness. -/
theorem elementaryClosureClass_orderedRamsey
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hAirr : A.Irreducible)
    (hB : ALinear A B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : Structure (closureLanguage L) W),
      ElementaryClosureClass A C ∧
      Structure.Arrow
        (targetClosureExpansion A A).withLinearOrder
        (targetClosureExpansion A B).withLinearOrder
        (@Structure.withLinearOrder (closureLanguage L) W C o.toLT) κ := by
  exact
    (elementaryClosureClass_freeAmalgamation hAirr).orderedRamsey_of_mem_target
      (targetClosureExpansion A A)
      (targetClosureExpansion A B)
      (targetClosureExpansion_mem hB)
      closureLanguage_positiveFuncArity κ

end StructuralRamsey.Girth
