import Girth.ClosureExpansion
import Girth.TreeGeometry
import PartiteConstruction.Iterated.FreeAmalgam

/-! # Elementary closure embeddings and free-amalgam sides

This module develops the reusable pieces needed to show that elementary
A-closure expansions form a free-amalgamation class.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U D E F C : Type v}

/-- An induced relational embedding with A-strong image lifts to a full
embedding of the elementary c_A closure expansions. -/
def elementaryClosureEmbeddingOfStrong
    {A : RelStructure L U} {D₀ : RelStructure L D}
    {E₀ : RelStructure L E}
    (e : RelStructure.Embedding D₀ E₀)
    (hStrong : AStrong A E₀ (copyCarrier e)) :
    StructuralRamsey.Structure.Embedding
      (elementaryClosureExpansion A D₀)
      (elementaryClosureExpansion A E₀) where
  toFun := e
  injective := e.injective
  map_rel_iff R x := e.map_rel_iff R x
  map_func := by
    intro Fsym x
    cases Fsym with
    | cB =>
        simp only [closureLanguage] at x
        simp [elementaryClosureExpansion,
          StructuralRamsey.Structure.imageSet]
    | cA =>
        simp only [closureLanguage] at x
        change
          StructuralRamsey.Structure.imageSet e (cAValue A D₀ x) =
            cAValue A E₀ (e ∘ x)
        apply Set.ext
        intro y
        constructor
        · rintro ⟨z, hz, rfl⟩
          rcases hz with ⟨hxy, a, h0, h1, hz⟩
          have hxy' : e (x 0) ≠ e (x 1) := by
            intro heq
            exact hxy (e.injective heq)
          refine ⟨hxy', e.comp a, ?_, ?_, ?_⟩
          · rcases h0 with ⟨t, ht⟩
            exact ⟨t, congrArg e ht⟩
          · rcases h1 with ⟨t, ht⟩
            exact ⟨t, congrArg e ht⟩
          · rcases hz with ⟨t, ht⟩
            exact ⟨t, congrArg e ht⟩
        · intro hy
          rcases hy with ⟨hxy, b, h0, h1, hyb⟩
          have hMeet :
              ¬ (copyCarrier b ∩ copyCarrier e).Subsingleton := by
            intro hs
            exact hxy (hs
              ⟨h0, ⟨x 0, rfl⟩⟩
              ⟨h1, ⟨x 1, rfl⟩⟩)
          have hbSub : copyCarrier b ⊆ copyCarrier e :=
            hStrong b hMeet
          have hfactor : ∀ a : U, ∃ d : D, b a = e d := by
            intro a
            rcases hbSub ⟨a, rfl⟩ with ⟨d, hd⟩
            exact ⟨d, hd.symm⟩
          let bD : RelStructure.Embedding A D₀ :=
            b.factorThroughRange e hfactor
          have hbD (a : U) : b a = e (bD a) :=
            Classical.choose_spec (hfactor a)
          have hxySrc : x 0 ≠ x 1 := by
            intro heq
            apply hxy
            exact congrArg e heq
          have h0D : x 0 ∈ copyCarrier bD := by
            rcases h0 with ⟨a0, ha0⟩
            refine ⟨a0, ?_⟩
            apply e.injective
            calc
              e (bD a0) = b a0 := (hbD a0).symm
              _ = e (x 0) := ha0
          have h1D : x 1 ∈ copyCarrier bD := by
            rcases h1 with ⟨a1, ha1⟩
            refine ⟨a1, ?_⟩
            apply e.injective
            calc
              e (bD a1) = b a1 := (hbD a1).symm
              _ = e (x 1) := ha1
          have hyE : y ∈ copyCarrier e := hbSub hyb
          rcases hyE with ⟨z, hz⟩
          refine ⟨z, ?_, hz⟩
          have hzD : z ∈ copyCarrier bD := by
            rcases hyb with ⟨az, haz⟩
            refine ⟨az, ?_⟩
            apply e.injective
            calc
              e (bD az) = b az := (hbD az).symm
              _ = y := haz
              _ = e z := hz.symm
          exact ⟨hxySrc, bD, h0D, h1D, hzD⟩

@[simp]
theorem elementaryClosureEmbeddingOfStrong_apply
    {A : RelStructure L U} {D₀ : RelStructure L D}
    {E₀ : RelStructure L E}
    (e : RelStructure.Embedding D₀ E₀)
    (hStrong : AStrong A E₀ (copyCarrier e))
    (x : D) :
    elementaryClosureEmbeddingOfStrong e hStrong x = e x :=
  rfl



/-- In a relational free amalgam, if the base is A-strong on the right,
then the left side remains A-strong in the whole amalgam. -/
theorem freeAmalgam_left_aStrong
    {A : RelStructure L U}
    {Base : RelStructure L D}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {fL : Embedding Base Left} {fR : Embedding Base Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hA : A.Irreducible)
    (hBaseR : AStrong A Right (copyCarrier fR))
    (hfree : IsFreeAmalgam fL fR iL iR) :
    AStrong A Whole (copyCarrier iL) := by
  intro a hMeet
  rcases irreducibleCopy_side_of_freeAmalgam hfree hA a with
    ⟨aL, haL⟩ | ⟨aR, haR⟩
  · intro x hx
    change copyCarrier a = copyCarrier (iL.comp aL) at haL
    rw [haL] at hx
    rcases hx with ⟨u, hu⟩
    exact ⟨aL u, hu⟩
  · have hMeetR :
        ¬ (copyCarrier aR ∩ copyCarrier fR).Subsingleton := by
      intro hs
      apply hMeet
      intro x hx y hy
      change copyCarrier a = copyCarrier (iR.comp aR) at haR
      have hxR : x ∈ copyCarrier (iR.comp aR) := by
        rw [← haR]
        exact hx.1
      have hyR : y ∈ copyCarrier (iR.comp aR) := by
        rw [← haR]
        exact hy.1
      rcases hxR with ⟨ux, hux⟩
      rcases hyR with ⟨uy, huy⟩
      rcases hx.2 with ⟨lx, hlx⟩
      rcases hy.2 with ⟨ly, hly⟩
      have hoverx :
          ∃ d : D, lx = fL d ∧ aR ux = fR d := by
        exact (hfree.overlap lx (aR ux)).mp
          (hlx.trans hux.symm)
      have hovery :
          ∃ d : D, ly = fL d ∧ aR uy = fR d := by
        exact (hfree.overlap ly (aR uy)).mp
          (hly.trans huy.symm)
      rcases hoverx with ⟨dx, _, hdx⟩
      rcases hovery with ⟨dy, _, hdy⟩
      have hEqR : aR ux = aR uy := hs
        ⟨⟨ux, rfl⟩, ⟨dx, hdx.symm⟩⟩
        ⟨⟨uy, rfl⟩, ⟨dy, hdy.symm⟩⟩
      calc
        x = iR (aR ux) := hux.symm
        _ = iR (aR uy) := congrArg iR hEqR
        _ = y := huy
    have hSubR : copyCarrier aR ⊆ copyCarrier fR :=
      hBaseR aR hMeetR
    intro x hx
    change copyCarrier a = copyCarrier (iR.comp aR) at haR
    rw [haR] at hx
    rcases hx with ⟨u, hu⟩
    have huBase := hSubR ⟨u, rfl⟩
    rcases huBase with ⟨d, hd⟩
    refine ⟨fL d, ?_⟩
    have hov :
        iL (fL d) = iR (aR u) := by
      apply (hfree.overlap (fL d) (aR u)).mpr
      exact ⟨d, rfl, hd.symm⟩
    exact hov.trans hu

/-- Symmetric version: if the base is A-strong on the left, then the right
side remains A-strong in the whole amalgam. -/
theorem freeAmalgam_right_aStrong
    {A : RelStructure L U}
    {Base : RelStructure L D}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {fL : Embedding Base Left} {fR : Embedding Base Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hA : A.Irreducible)
    (hBaseL : AStrong A Left (copyCarrier fL))
    (hfree : IsFreeAmalgam fL fR iL iR) :
    AStrong A Whole (copyCarrier iR) := by
  intro a hMeet
  rcases irreducibleCopy_side_of_freeAmalgam hfree hA a with
    ⟨aL, haL⟩ | ⟨aR, haR⟩
  · have hMeetL :
        ¬ (copyCarrier aL ∩ copyCarrier fL).Subsingleton := by
      intro hs
      apply hMeet
      intro x hx y hy
      change copyCarrier a = copyCarrier (iL.comp aL) at haL
      have hxL : x ∈ copyCarrier (iL.comp aL) := by
        rw [← haL]
        exact hx.1
      have hyL : y ∈ copyCarrier (iL.comp aL) := by
        rw [← haL]
        exact hy.1
      rcases hxL with ⟨ux, hux⟩
      rcases hyL with ⟨uy, huy⟩
      rcases hx.2 with ⟨rx, hrx⟩
      rcases hy.2 with ⟨ry, hry⟩
      have hoverx :
          ∃ d : D, aL ux = fL d ∧ rx = fR d := by
        exact (hfree.overlap (aL ux) rx).mp
          (hux.trans hrx.symm)
      have hovery :
          ∃ d : D, aL uy = fL d ∧ ry = fR d := by
        exact (hfree.overlap (aL uy) ry).mp
          (huy.trans hry.symm)
      rcases hoverx with ⟨dx, hdx, _⟩
      rcases hovery with ⟨dy, hdy, _⟩
      have hEqL : aL ux = aL uy := hs
        ⟨⟨ux, rfl⟩, ⟨dx, hdx.symm⟩⟩
        ⟨⟨uy, rfl⟩, ⟨dy, hdy.symm⟩⟩
      calc
        x = iL (aL ux) := hux.symm
        _ = iL (aL uy) := congrArg iL hEqL
        _ = y := huy
    have hSubL : copyCarrier aL ⊆ copyCarrier fL :=
      hBaseL aL hMeetL
    intro x hx
    change copyCarrier a = copyCarrier (iL.comp aL) at haL
    rw [haL] at hx
    rcases hx with ⟨u, hu⟩
    have huBase := hSubL ⟨u, rfl⟩
    rcases huBase with ⟨d, hd⟩
    refine ⟨fR d, ?_⟩
    have hov :
        iR (fR d) = iL (aL u) := by
      symm
      apply (hfree.overlap (aL u) (fR d)).mpr
      exact ⟨d, hd.symm, rfl⟩
    exact hov.trans hu
  · intro x hx
    change copyCarrier a = copyCarrier (iR.comp aR) at haR
    rw [haR] at hx
    rcases hx with ⟨u, hu⟩
    exact ⟨aR u, hu⟩

/-- Free amalgamation over A-strong bases preserves A-linearity. -/
theorem aLinear_of_freeAmalgam
    {A : RelStructure L U}
    {Base : RelStructure L D}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {fL : Embedding Base Left} {fR : Embedding Base Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hA : A.Irreducible)
    (hLeft : ALinear A Left)
    (hRight : ALinear A Right)
    (hBaseL : AStrong A Left (copyCarrier fL))
    (hBaseR : AStrong A Right (copyCarrier fR))
    (hfree : IsFreeAmalgam fL fR iL iR) :
    ALinear A Whole := by
  have hStrongL : AStrong A Whole (copyCarrier iL) :=
    freeAmalgam_left_aStrong hA hBaseR hfree
  have hStrongR : AStrong A Whole (copyCarrier iR) :=
    freeAmalgam_right_aStrong hA hBaseL hfree
  intro a b hne
  by_contra hMeet
  rcases irreducibleCopy_side_of_freeAmalgam hfree hA a with
    ⟨aL, haL⟩ | ⟨aR, haR⟩
  · rcases irreducibleCopy_side_of_freeAmalgam hfree hA b with
      ⟨bL, hbL⟩ | ⟨bR, hbR⟩
    · have haSub : copyCarrier a ⊆ copyCarrier iL := by
        change copyCarrier a = copyCarrier (iL.comp aL) at haL
        rw [haL]
        rintro x ⟨u, rfl⟩
        exact ⟨aL u, rfl⟩
      have hbSub : copyCarrier b ⊆ copyCarrier iL := by
        change copyCarrier b = copyCarrier (iL.comp bL) at hbL
        rw [hbL]
        rintro x ⟨u, rfl⟩
        exact ⟨bL u, rfl⟩
      exact hne (sameCopy_of_contained_and_not_subsingleton
        hLeft a b iL haSub hbSub hMeet)
    · have haMeetR :
          ¬ (copyCarrier a ∩ copyCarrier iR).Subsingleton := by
        intro hs
        apply hMeet
        intro x hx y hy
        apply hs
        · exact ⟨hx.1, by
            change copyCarrier b = copyCarrier (iR.comp bR) at hbR
            rw [hbR] at hx
            rcases hx.2 with ⟨u, hu⟩
            exact ⟨bR u, hu⟩⟩
        · exact ⟨hy.1, by
            change copyCarrier b = copyCarrier (iR.comp bR) at hbR
            rw [hbR] at hy
            rcases hy.2 with ⟨u, hu⟩
            exact ⟨bR u, hu⟩⟩
      have haSub : copyCarrier a ⊆ copyCarrier iR :=
        hStrongR a haMeetR
      have hbSub : copyCarrier b ⊆ copyCarrier iR := by
        change copyCarrier b = copyCarrier (iR.comp bR) at hbR
        rw [hbR]
        rintro x ⟨u, rfl⟩
        exact ⟨bR u, rfl⟩
      exact hne (sameCopy_of_contained_and_not_subsingleton
        hRight a b iR haSub hbSub hMeet)
  · rcases irreducibleCopy_side_of_freeAmalgam hfree hA b with
      ⟨bL, hbL⟩ | ⟨bR, hbR⟩
    · have haMeetL :
          ¬ (copyCarrier a ∩ copyCarrier iL).Subsingleton := by
        intro hs
        apply hMeet
        intro x hx y hy
        apply hs
        · exact ⟨hx.1, by
            change copyCarrier b = copyCarrier (iL.comp bL) at hbL
            rw [hbL] at hx
            rcases hx.2 with ⟨u, hu⟩
            exact ⟨bL u, hu⟩⟩
        · exact ⟨hy.1, by
            change copyCarrier b = copyCarrier (iL.comp bL) at hbL
            rw [hbL] at hy
            rcases hy.2 with ⟨u, hu⟩
            exact ⟨bL u, hu⟩⟩
      have haSub : copyCarrier a ⊆ copyCarrier iL :=
        hStrongL a haMeetL
      have hbSub : copyCarrier b ⊆ copyCarrier iL := by
        change copyCarrier b = copyCarrier (iL.comp bL) at hbL
        rw [hbL]
        rintro x ⟨u, rfl⟩
        exact ⟨bL u, rfl⟩
      exact hne (sameCopy_of_contained_and_not_subsingleton
        hLeft a b iL haSub hbSub hMeet)
    · have haSub : copyCarrier a ⊆ copyCarrier iR := by
        change copyCarrier a = copyCarrier (iR.comp aR) at haR
        rw [haR]
        rintro x ⟨u, rfl⟩
        exact ⟨aR u, rfl⟩
      have hbSub : copyCarrier b ⊆ copyCarrier iR := by
        change copyCarrier b = copyCarrier (iR.comp bR) at hbR
        rw [hbR]
        rintro x ⟨u, rfl⟩
        exact ⟨bR u, rfl⟩
      exact hne (sameCopy_of_contained_and_not_subsingleton
        hRight a b iR haSub hbSub hMeet)

/-- The concrete relational free amalgam of two A-linear structures over
A-strong base images is again A-linear, and both side embeddings are A-strong.
-/
theorem concreteElementaryClosureAmalgam_geometry
    {A : RelStructure L U}
    {Base : RelStructure L D}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    (hA : A.Irreducible)
    (hLeft : ALinear A Left)
    (hRight : ALinear A Right)
    (fL : Embedding Base Left) (fR : Embedding Base Right)
    (hBaseL : AStrong A Left (copyCarrier fL))
    (hBaseR : AStrong A Right (copyCarrier fR)) :
    let Whole :=
      RelStructure.FreeAmalgam.amalgam Base Left Right fL fR
    let iL :=
      RelStructure.FreeAmalgam.leftEmbedding Base Left Right fL fR
    let iR :=
      RelStructure.FreeAmalgam.rightEmbedding Base Left Right fL fR
    ALinear A Whole ∧
      AStrong A Whole (copyCarrier iL) ∧
      AStrong A Whole (copyCarrier iR) := by
  dsimp
  let hfree :=
    RelStructure.FreeAmalgam.isFreeAmalgam Base Left Right fL fR
  exact ⟨aLinear_of_freeAmalgam hA hLeft hRight
      hBaseL hBaseR hfree,
    freeAmalgam_left_aStrong hA hBaseR hfree,
    freeAmalgam_right_aStrong hA hBaseL hfree⟩


/-- The elementary c_A expansions form a genuine free amalgam whenever the
relational base images are A-strong. -/
theorem elementaryClosure_isFreeAmalgam
    {A : RelStructure L U}
    {Base : RelStructure L D}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {fL : Embedding Base Left} {fR : Embedding Base Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hA : A.Irreducible)
    (hBaseL : AStrong A Left (copyCarrier fL))
    (hBaseR : AStrong A Right (copyCarrier fR))
    (hfree : IsFreeAmalgam fL fR iL iR) :
    StructuralRamsey.Structure.IsFreeAmalgam
      (elementaryClosureEmbeddingOfStrong fL hBaseL)
      (elementaryClosureEmbeddingOfStrong fR hBaseR)
      (elementaryClosureEmbeddingOfStrong iL
        (freeAmalgam_left_aStrong hA hBaseR hfree))
      (elementaryClosureEmbeddingOfStrong iR
        (freeAmalgam_right_aStrong hA hBaseL hfree)) := by
  let fLf :=
    elementaryClosureEmbeddingOfStrong fL hBaseL
  let fRf :=
    elementaryClosureEmbeddingOfStrong fR hBaseR
  let iLf :=
    elementaryClosureEmbeddingOfStrong iL
      (freeAmalgam_left_aStrong hA hBaseR hfree)
  let iRf :=
    elementaryClosureEmbeddingOfStrong iR
      (freeAmalgam_right_aStrong hA hBaseL hfree)
  change StructuralRamsey.Structure.IsFreeAmalgam fLf fRf iLf iRf
  refine {
    covers := ?_
    overlap := ?_
    rel_iff := ?_
    func_iff := ?_
  }
  · intro z
    rcases hfree.covers z with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨y, hy⟩
  · intro x y
    exact hfree.overlap x y
  · intro R z
    exact hfree.rel_iff R z
  · intro Fsym x y
    cases Fsym with
    | cB =>
        simp [elementaryClosureExpansion]
    | cA =>
        simp only [closureLanguage] at x
        change
          y ∈ cAValue A Whole x ↔
            (∃ a : Fin 2 → E, ∃ b : E,
              b ∈ cAValue A Left a ∧
              x = iL ∘ a ∧ y = iL b) ∨
            (∃ a : Fin 2 → F, ∃ b : F,
              b ∈ cAValue A Right a ∧
              x = iR ∘ a ∧ y = iR b)
        constructor
        · intro hy
          rcases hy with ⟨hxy, a, h0, h1, hy⟩
          rcases irreducibleCopy_side_of_freeAmalgam hfree hA a with
            ⟨aL, haL⟩ | ⟨aR, haR⟩
          · change copyCarrier a = copyCarrier (iL.comp aL) at haL
            have h0' : x 0 ∈ copyCarrier (iL.comp aL) := by
              rw [← haL]
              exact h0
            have h1' : x 1 ∈ copyCarrier (iL.comp aL) := by
              rw [← haL]
              exact h1
            have hy' : y ∈ copyCarrier (iL.comp aL) := by
              rw [← haL]
              exact hy
            rcases h0' with ⟨u0, hu0⟩
            rcases h1' with ⟨u1, hu1⟩
            rcases hy' with ⟨uy, huy⟩
            let args : Fin 2 → E := ![aL u0, aL u1]
            refine Or.inl ⟨args, aL uy, ?_, ?_, ?_⟩
            · refine ⟨?_, aL, ?_, ?_, ?_⟩
              · intro heq
                apply hxy
                calc
                  x 0 = iL (aL u0) := hu0.symm
                  _ = iL (aL u1) := congrArg iL heq
                  _ = x 1 := hu1
              · exact ⟨u0, rfl⟩
              · exact ⟨u1, rfl⟩
              · exact ⟨uy, rfl⟩
            · funext j
              fin_cases j
              · exact hu0.symm
              · exact hu1.symm
            · exact huy.symm
          · change copyCarrier a = copyCarrier (iR.comp aR) at haR
            have h0' : x 0 ∈ copyCarrier (iR.comp aR) := by
              rw [← haR]
              exact h0
            have h1' : x 1 ∈ copyCarrier (iR.comp aR) := by
              rw [← haR]
              exact h1
            have hy' : y ∈ copyCarrier (iR.comp aR) := by
              rw [← haR]
              exact hy
            rcases h0' with ⟨u0, hu0⟩
            rcases h1' with ⟨u1, hu1⟩
            rcases hy' with ⟨uy, huy⟩
            let args : Fin 2 → F := ![aR u0, aR u1]
            refine Or.inr ⟨args, aR uy, ?_, ?_, ?_⟩
            · refine ⟨?_, aR, ?_, ?_, ?_⟩
              · intro heq
                apply hxy
                calc
                  x 0 = iR (aR u0) := hu0.symm
                  _ = iR (aR u1) := congrArg iR heq
                  _ = x 1 := hu1
              · exact ⟨u0, rfl⟩
              · exact ⟨u1, rfl⟩
              · exact ⟨uy, rfl⟩
            · funext j
              fin_cases j
              · exact hu0.symm
              · exact hu1.symm
            · exact huy.symm
        · rintro (⟨args, b, hb, hx, hy⟩ | ⟨args, b, hb, hx, hy⟩)
          · rcases hb with ⟨hneq, a, h0, h1, hb⟩
            refine ⟨?_, iL.comp a, ?_, ?_, ?_⟩
            · intro hEq
              apply hneq
              apply iL.injective
              calc
                iL (args 0) = x 0 := (congrFun hx 0).symm
                _ = x 1 := hEq
                _ = iL (args 1) := congrFun hx 1
            · rcases h0 with ⟨u, hu⟩
              refine ⟨u, ?_⟩
              calc
                iL (a u) = iL (args 0) := congrArg iL hu
                _ = x 0 := (congrFun hx 0).symm
            · rcases h1 with ⟨u, hu⟩
              refine ⟨u, ?_⟩
              calc
                iL (a u) = iL (args 1) := congrArg iL hu
                _ = x 1 := (congrFun hx 1).symm
            · rcases hb with ⟨u, hu⟩
              refine ⟨u, ?_⟩
              calc
                iL (a u) = iL b := congrArg iL hu
                _ = y := hy.symm
          · rcases hb with ⟨hneq, a, h0, h1, hb⟩
            refine ⟨?_, iR.comp a, ?_, ?_, ?_⟩
            · intro hEq
              apply hneq
              apply iR.injective
              calc
                iR (args 0) = x 0 := (congrFun hx 0).symm
                _ = x 1 := hEq
                _ = iR (args 1) := congrFun hx 1
            · rcases h0 with ⟨u, hu⟩
              refine ⟨u, ?_⟩
              calc
                iR (a u) = iR (args 0) := congrArg iR hu
                _ = x 0 := (congrFun hx 0).symm
            · rcases h1 with ⟨u, hu⟩
              refine ⟨u, ?_⟩
              calc
                iR (a u) = iR (args 1) := congrArg iR hu
                _ = x 1 := (congrFun hx 1).symm
            · rcases hb with ⟨u, hu⟩
              refine ⟨u, ?_⟩
              calc
                iR (a u) = iR b := congrArg iR hu
                _ = y := hy.symm

/-- Concrete free amalgamation for elementary closure expansions.  The
underlying relational whole is the canonical relational free amalgam. -/
theorem concreteElementaryClosure_freeAmalgam
    {A : RelStructure L U}
    {Base : RelStructure L D}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    (hA : A.Irreducible)
    (hLeft : ALinear A Left)
    (hRight : ALinear A Right)
    (fL : Embedding Base Left) (fR : Embedding Base Right)
    (hBaseL : AStrong A Left (copyCarrier fL))
    (hBaseR : AStrong A Right (copyCarrier fR)) :
    let Whole :=
      RelStructure.FreeAmalgam.amalgam Base Left Right fL fR
    let iL :=
      RelStructure.FreeAmalgam.leftEmbedding Base Left Right fL fR
    let iR :=
      RelStructure.FreeAmalgam.rightEmbedding Base Left Right fL fR
    ALinear A Whole ∧
      StructuralRamsey.Structure.IsFreeAmalgam
        (elementaryClosureEmbeddingOfStrong fL hBaseL)
        (elementaryClosureEmbeddingOfStrong fR hBaseR)
        (elementaryClosureEmbeddingOfStrong iL
          (freeAmalgam_left_aStrong hA hBaseR
            (RelStructure.FreeAmalgam.isFreeAmalgam
              Base Left Right fL fR)))
        (elementaryClosureEmbeddingOfStrong iR
          (freeAmalgam_right_aStrong hA hBaseL
            (RelStructure.FreeAmalgam.isFreeAmalgam
              Base Left Right fL fR))) := by
  dsimp
  let hfree :=
    RelStructure.FreeAmalgam.isFreeAmalgam Base Left Right fL fR
  exact ⟨aLinear_of_freeAmalgam hA hLeft hRight
      hBaseL hBaseR hfree,
    elementaryClosure_isFreeAmalgam hA hBaseL hBaseR hfree⟩


/-- A closed induced substructure of an elementary closure expansion is exactly
the elementary closure expansion of its relational reduct.  The embedding is
the identity on the subtype carrier. -/
def elementaryClosure_induceEmbedding
    {A : RelStructure L U} {D₀ : RelStructure L D}
    (S : Set D)
    (hClosed : (elementaryClosureExpansion A D₀).IsClosed S) :
    StructuralRamsey.Structure.Embedding
      (elementaryClosureExpansion A (D₀.induce S))
      ((elementaryClosureExpansion A D₀).induce S hClosed) where
  toFun := id
  injective := Function.injective_id
  map_rel_iff R x := Iff.rfl
  map_func := by
    intro Fsym x
    cases Fsym with
    | cB =>
        simp only [closureLanguage] at x
        apply Set.ext
        intro y
        constructor
        · rintro ⟨z, hz, rfl⟩
          change z ∈ (∅ : Set S) at hz
          exact hz.elim
        · intro hy
          change y.1 ∈ (∅ : Set D) at hy
          exact hy.elim
    | cA =>
        simp only [closureLanguage] at x
        let incl : RelStructure.Embedding (D₀.induce S) D₀ :=
          RelStructure.inclusion D₀ S
        have hStrong : AStrong A D₀ S :=
          (elementaryClosure_isClosed_iff_aStrong A D₀ S).mp hClosed
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          rcases hz with ⟨hxy, a, h0, h1, hz⟩
          change y.1 ∈ cAValue A D₀ (Subtype.val ∘ x)
          refine ⟨?_, incl.comp a, ?_, ?_, ?_⟩
          · intro heq
            apply hxy
            apply Subtype.ext
            exact heq
          · rcases h0 with ⟨u, hu⟩
            exact ⟨u, congrArg Subtype.val hu⟩
          · rcases h1 with ⟨u, hu⟩
            exact ⟨u, congrArg Subtype.val hu⟩
          · rcases hz with ⟨u, hu⟩
            exact ⟨u, congrArg Subtype.val hu⟩
        · intro hy
          change y.1 ∈ cAValue A D₀ (Subtype.val ∘ x) at hy
          rcases hy with ⟨hxy, b, h0, h1, hyb⟩
          have hMeet :
              ¬ (copyCarrier b ∩ S).Subsingleton := by
            intro hs
            have h0S : (Subtype.val (x 0)) ∈ S := (x 0).2
            have h1S : (Subtype.val (x 1)) ∈ S := (x 1).2
            have heq : Subtype.val (x 0) = Subtype.val (x 1) :=
              hs ⟨h0, h0S⟩ ⟨h1, h1S⟩
            apply hxy
            exact heq
          have hbSub : copyCarrier b ⊆ S :=
            hStrong b hMeet
          have hfactor : ∀ a : U, ∃ s : S, b a = incl s := by
            intro a
            have hmem := hbSub ⟨a, rfl⟩
            exact ⟨⟨b a, hmem⟩, rfl⟩
          let bS : RelStructure.Embedding A (D₀.induce S) :=
            b.factorThroughRange incl hfactor
          have hbS (a : U) : b a = incl (bS a) :=
            Classical.choose_spec (hfactor a)
          have h0S : x 0 ∈ copyCarrier bS := by
            rcases h0 with ⟨a0, ha0⟩
            refine ⟨a0, ?_⟩
            apply Subtype.ext
            calc
              (bS a0).1 = b a0 := (hbS a0).symm
              _ = (x 0).1 := ha0
          have h1S : x 1 ∈ copyCarrier bS := by
            rcases h1 with ⟨a1, ha1⟩
            refine ⟨a1, ?_⟩
            apply Subtype.ext
            calc
              (bS a1).1 = b a1 := (hbS a1).symm
              _ = (x 1).1 := ha1
          have hyS : y ∈ copyCarrier bS := by
            rcases hyb with ⟨ay, hay⟩
            refine ⟨ay, ?_⟩
            apply Subtype.ext
            calc
              (bS ay).1 = b ay := (hbS ay).symm
              _ = y.1 := hay
          have hxyS : x 0 ≠ x 1 := by
            intro heq
            apply hxy
            exact congrArg Subtype.val heq
          change y ∈
            StructuralRamsey.Structure.imageSet id
              (cAValue A (D₀.induce S) x)
          exact ⟨y, ⟨hxyS, bS, h0S, h1S, hyS⟩, rfl⟩

/-- Consequently, closed induced reducts of A-linear elementary closure
structures are again A-linear. -/
theorem elementaryClosure_closed_induce_aLinear
    {A : RelStructure L U} {D₀ : RelStructure L D}
    (hLinear : ALinear A D₀)
    (S : Set D)
    (_hClosed : (elementaryClosureExpansion A D₀).IsClosed S) :
    ALinear A (D₀.induce S) :=
  aLinear_induce hLinear S
end StructuralRamsey.Girth
