import Girth.Berge
import Mathlib.Tactic

/-!
# Track 1: three-edge closure of strong free support amalgams

The canonical c_A class already has checked A-linearity under free
amalgamation.  This isolates the additional girth>3 step at the
PHYSICAL SUPPORT FAMILY level. A mixed Berge triangle has two
edges on one side. The remaining edge meets the common domain
in two distinct connectors, hence belongs to the first side
under the strong-overlap reflection hypotheses.

This lemma is deliberately conditional: the *actual* functional free
amalgam must supply cross-edge contacts in S, reflection of any edge
meeting S twice, and global girth>2. No proof of those adapters
or of the EHN class is claimed by this module alone.

DRAFT / UNCOMPILED. Do not treat #print axioms as executed.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- No new Berge triangle appears across a strong free interface.
The global two-cycle exclusion is a separate already-known
linearity endpoint. -/
theorem girthGT_three_union_of_strong_overlap
    (HL HR : Set (Set W)) (S : Set W)
    (hL : GirthGT HL 3) (hR : GirthGT HR 3)
    (hUnionTwo : GirthGT (HL ∪ HR) 2)
    (hCross : ∀ ⦃e f : Set W⦄, e ∈ HL → f ∈ HR → e ∩ f ⊆ S)
    (hReflectR : ∀ ⦃e : Set W⦄, e ∈ HR →
       ¬ (e ∩ S).Subsingleton → e ∈ HL)
    (hReflectL : ∀ ⦃e : Set W⦄, e ∈ HL →
       ¬ (e ∩ S).Subsingleton → e ∈ HR) :
    GirthGT (HL ∪ HR) 3 := by
  classical
  rintro ⟨c, hlen⟩
  have hlength : c.length = 2 ∨ c.length = 3 := by
    have := c.hlength
    omega
  rcases hlength with htwo | hthree
  · exact hUnionTwo ⟨c, by omega⟩
  let i0 : Fin c.length := ⟨0, by omega⟩
  let i1 : Fin c.length := ⟨1, by omega⟩
  let i2 : Fin c.length := ⟨2, by omega⟩
  let e0 := c.edge i0
  let e1 := c.edge i1
  let e2 := c.edge i2
  let v0 := c.vertex i0
  let v1 := c.vertex i1
  let v2 := c.vertex i2
  have hn0 : cyclicSucc i0 = i1 := by
    apply Fin.ext
    simp [cyclicSucc, i0, i1, hthree]
  have hn1 : cyclicSucc i1 = i2 := by
    apply Fin.ext
    simp [cyclicSucc, i1, i2, hthree]
  have hn2 : cyclicSucc i2 = i0 := by
    apply Fin.ext
    simp [cyclicSucc, i2, i0, hthree]
  have hv0e0 : v0 ∈ e0 := c.left_mem i0
  have hv0e1 : v0 ∈ e1 := by
    simpa only [v0, e1, hn0] using c.right_mem i0
  have hv1e1 : v1 ∈ e1 := c.left_mem i1
  have hv1e2 : v1 ∈ e2 := by
    simpa only [v1, e2, hn1] using c.right_mem i1
  have hv2e2 : v2 ∈ e2 := c.left_mem i2
  have hv2e0 : v2 ∈ e0 := by
    simpa only [v2, e0, hn2] using c.right_mem i2
  have hv01 : v0 ≠ v1 := by
    intro h
    have hh := c.vertex_injective h
    have hv := congrArg Fin.val hh
    dsimp [i0, i1] at hv
    omega
  have hv02 : v0 ≠ v2 := by
    intro h
    have hh := c.vertex_injective h
    have hv := congrArg Fin.val hh
    dsimp [i0, i2] at hv
    omega
  have hv12 : v1 ≠ v2 := by
    intro h
    have hh := c.vertex_injective h
    have hv := congrArg Fin.val hh
    dsimp [i1, i2] at hv
    omega
  have hToLeft (e : Set W) (he : e ∈ HR)
      (a b : Set W) (ha : a ∈ HL) (hb : b ∈ HL)
      (x y : W) (hxe : x ∈ e) (hxa : x ∈ a)
      (hye : y ∈ e) (hyb : y ∈ b)
      (hxy : x ≠ y) : e ∈ HL := by
    have hxS : x ∈ S := hCross ha he ⟨hxa, hxe⟩
    have hyS : y ∈ S := hCross hb he ⟨hyb, hye⟩
    apply hReflectR he
    intro hs
    exact hxy (hs ⟨hxe, hxS⟩ ⟨hye, hyS⟩)
  have hToRight (e : Set W) (he : e ∈ HL)
      (a b : Set W) (ha : a ∈ HR) (hb : b ∈ HR)
      (x y : W) (hxe : x ∈ e) (hxa : x ∈ a)
      (hye : y ∈ e) (hyb : y ∈ b)
      (hxy : x ≠ y) : e ∈ HR := by
    have hxS : x ∈ S := hCross he ha ⟨hxe, hxa⟩
    have hyS : y ∈ S := hCross he hb ⟨hye, hyb⟩
    apply hReflectL he
    intro hs
    exact hxy (hs ⟨hxe, hxS⟩ ⟨hye, hyS⟩)
  have hAllLeft (h0 : e0 ∈ HL) (h1 : e1 ∈ HL)
      (h2 : e2 ∈ HL) : False := by
    apply hL
    refine ⟨c.ofEdgeMem ?_, hlen⟩
    intro i
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
      have := i.isLt
      omega
    rcases hi with hi | hi | hi
    · have hh : i = i0 := Fin.ext hi
      simpa only [hh] using h0
    · have hh : i = i1 := Fin.ext hi
      simpa only [hh] using h1
    · have hh : i = i2 := Fin.ext hi
      simpa only [hh] using h2
  have hAllRight (h0 : e0 ∈ HR) (h1 : e1 ∈ HR)
      (h2 : e2 ∈ HR) : False := by
    apply hR
    refine ⟨c.ofEdgeMem ?_, hlen⟩
    intro i
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
      have := i.isLt
      omega
    rcases hi with hi | hi | hi
    · have hh : i = i0 := Fin.ext hi
      simpa only [hh] using h0
    · have hh : i = i1 := Fin.ext hi
      simpa only [hh] using h1
    · have hh : i = i2 := Fin.ext hi
      simpa only [hh] using h2
  rcases c.edge_mem i0 with h0L | h0R
  · rcases c.edge_mem i1 with h1L | h1R
    · rcases c.edge_mem i2 with h2L | h2R
      · exact hAllLeft h0L h1L h2L
      · have h2L := hToLeft e2 h2R e0 e1 h0L h1L
          v2 v1 hv2e2 hv2e0 hv1e2 hv1e1 hv12.symm
        exact hAllLeft h0L h1L h2L
    · rcases c.edge_mem i2 with h2L | h2R
      · have h1L := hToLeft e1 h1R e0 e2 h0L h2L
          v0 v1 hv0e1 hv0e0 hv1e1 hv1e2 hv01
        exact hAllLeft h0L h1L h2L
      · have h0R := hToRight e0 h0L e1 e2 h1R h2R
          v0 v2 hv0e0 hv0e1 hv2e0 hv2e2 hv02
        exact hAllRight h0R h1R h2R
  · rcases c.edge_mem i1 with h1L | h1R
    · rcases c.edge_mem i2 with h2L | h2R
      · have h0L := hToLeft e0 h0R e1 e2 h1L h2L
          v0 v2 hv0e0 hv0e1 hv2e0 hv2e2 hv02
        exact hAllLeft h0L h1L h2L
      · have h1R := hToRight e1 h1L e0 e2 h0R h2R
          v0 v1 hv0e1 hv0e0 hv1e1 hv1e2 hv01
        exact hAllRight h0R h1R h2R
    · rcases c.edge_mem i2 with h2L | h2R
      · have h2R := hToRight e2 h2L e0 e1 h0R h1R
          v2 v1 hv2e2 hv2e0 hv1e2 hv1e1 hv12.symm
        exact hAllRight h0R h1R h2R
      · exact hAllRight h0R h1R h2R

#print axioms StructuralRamsey.Girth.girthGT_three_union_of_strong_overlap

end StructuralRamsey.Girth
