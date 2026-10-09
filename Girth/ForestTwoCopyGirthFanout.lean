import Girth.ForestOnePortFanout
import Girth.BergeGlue
import Mathlib.Tactic

/-!
# Berge girth preservation for explicit safe one-port B-copy fanout

The tagged left/right maps of the explicit two-copy construction
preserve Berge girth of each support edge family, because both maps
are injective. Every cross-side edge intersection lies in the tagged
port S.

Thus the verified pure Berge gluing lemmas imply girth preservation
over singleton ports, and also over complete old/new A-support edge
ports. Combined with the separate forest fanout lemma, this supplies
the two independent geometric invariants needed for a safe local
picture extension: designated-copy foresthood and ambient A-girth.

The result says nothing about the global successor-history
normalization, colour homogeneity, or whether extra relational A
copies appear after decoration.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Z : Type v}

/-- Image of a support hyperedge family under an injective vertex map. -/
def injectedEdgeFamily (φ : W ↪ Z) (H : Set (Set W)) :
    Set (Set Z) :=
  {e | ∃ a : Set W, a ∈ H ∧ e = φ '' a}

/-- Injective vertex transport cannot create a Berge cycle of bounded
length: its vertices and edge sets pull back uniquely. -/
theorem girthGT_injectedEdgeFamily
    (φ : W ↪ Z) (H : Set (Set W)) (g : ℕ)
    (hGirth : GirthGT H g) :
    GirthGT (injectedEdgeFamily φ H) g := by
  rintro ⟨c, hcLen⟩
  classical
  have hEdge (j : Fin c.length) :
      ∃ a : Set W, a ∈ H ∧ c.edge j = φ '' a :=
    c.edge_mem j
  choose oldEdge hOldEdge hImage using hEdge
  have hOldEdgeInj : Function.Injective oldEdge := by
    intro j k hjk
    apply c.edge_injective
    calc
      c.edge j = φ '' oldEdge j := hImage j
      _ = φ '' oldEdge k := congrArg (fun a : Set W => φ '' a) hjk
      _ = c.edge k := (hImage k).symm
  have hvExists (j : Fin c.length) :
      ∃ x : W, φ x = c.vertex j := by
    have hMem : c.vertex j ∈ φ '' oldEdge j := by
      rw [← hImage j]
      exact c.left_mem j
    obtain ⟨x, _, hx⟩ := hMem
    exact ⟨x, hx⟩
  let oldVertex : Fin c.length → W :=
    fun j => Classical.choose (hvExists j)
  have hOldVertexMap (j : Fin c.length) :
      φ (oldVertex j) = c.vertex j :=
    Classical.choose_spec (hvExists j)
  have hOldVertexInj : Function.Injective oldVertex := by
    intro j k hjk
    apply c.vertex_injective
    calc
      c.vertex j = φ (oldVertex j) := (hOldVertexMap j).symm
      _ = φ (oldVertex k) := congrArg φ hjk
      _ = c.vertex k := hOldVertexMap k
  have hLeft (j : Fin c.length) :
      oldVertex j ∈ oldEdge j := by
    have hv : φ (oldVertex j) ∈ φ '' oldEdge j := by
      rw [hOldVertexMap j, ← hImage j]
      exact c.left_mem j
    obtain ⟨x, hx, hmap⟩ := hv
    have hEq : oldVertex j = x := φ.injective hmap.symm
    simpa only [hEq] using hx
  have hRight (j : Fin c.length) :
      oldVertex j ∈ oldEdge (cyclicSucc j) := by
    have hv : φ (oldVertex j) ∈ φ '' oldEdge (cyclicSucc j) := by
      rw [hOldVertexMap j, ← hImage (cyclicSucc j)]
      exact c.right_mem j
    obtain ⟨x, hx, hmap⟩ := hv
    have hEq : oldVertex j = x := φ.injective hmap.symm
    simpa only [hEq] using hx
  let oldCycle : BergeCycle H :=
    { length := c.length
      hlength := c.hlength
      edge := oldEdge
      vertex := oldVertex
      edge_mem := hOldEdge
      edge_injective := hOldEdgeInj
      vertex_injective := hOldVertexInj
      left_mem := hLeft
      right_mem := hRight }
  exact hGirth ⟨oldCycle, hcLen⟩

/-- The image of a singleton/empty port is still subsingleton. -/
theorem twoCopyPort_separator_image_subsingleton
    (S : Set W) (hSmall : S.Subsingleton) :
    ((twoCopyPortLeft S) '' S).Subsingleton := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact congrArg (twoCopyPortLeft S) (hSmall ha hb)

/-- No cross-side A-support intersection can escape the physically
identified separator, regardless of the two source support families. -/
theorem twoCopyPort_edgeFamilies_cross_subset
    (HL HR : Set (Set W)) (S : Set W) :
    ∀ ⦃eL eR : Set (W × Bool)⦄,
      eL ∈ injectedEdgeFamily (twoCopyPortLeft S) HL →
      eR ∈ injectedEdgeFamily (twoCopyPortRight S) HR →
      eL ∩ eR ⊆ (twoCopyPortLeft S) '' S := by
  intro eL eR heL heR
  obtain ⟨a, _, rfl⟩ := heL
  obtain ⟨b, _, rfl⟩ := heR
  exact twoCopyPort_cross_inter_subset S a b

/-- The ambient union of old and new A-support edges preserves any
Berge girth cutoff when the new copy meets the old picture only at
one vertex (or not at all). -/
theorem twoCopyPort_girth_singleton_fanout
    (HL HR : Set (Set W)) (S : Set W) (g : ℕ)
    (hSmall : S.Subsingleton)
    (hOld : GirthGT HL g) (hNew : GirthGT HR g) :
    GirthGT
      (injectedEdgeFamily (twoCopyPortLeft S) HL ∪
       injectedEdgeFamily (twoCopyPortRight S) HR) g := by
  apply girthGT_union_of_subsingleton_glue
    (S := (twoCopyPortLeft S) '' S)
    (twoCopyPort_separator_image_subsingleton S hSmall)
    (twoCopyPort_edgeFamilies_cross_subset HL HR S)
    (girthGT_injectedEdgeFamily (twoCopyPortLeft S) HL g hOld)
    (girthGT_injectedEdgeFamily (twoCopyPortRight S) HR g hNew)

/-- The same conclusion holds when the port S is an actual COMPLETE
support A-edge on both sides. In this case its two images are literally
one shared ambient support edge. -/
theorem twoCopyPort_girth_Aedge_fanout
    (HL HR : Set (Set W)) (S : Set W) (g : ℕ)
    (hSLeft : S ∈ HL) (hSRight : S ∈ HR)
    (hOld : GirthGT HL g) (hNew : GirthGT HR g) :
    GirthGT
      (injectedEdgeFamily (twoCopyPortLeft S) HL ∪
       injectedEdgeFamily (twoCopyPortRight S) HR) g := by
  apply girthGT_union_of_edge_glue
    (separator := (twoCopyPortLeft S) '' S)
  · exact ⟨S, hSLeft, rfl⟩
  · exact ⟨S, hSRight, twoCopyPort_image_separator S⟩
  · exact twoCopyPort_edgeFamilies_cross_subset HL HR S
  · exact girthGT_injectedEdgeFamily (twoCopyPortLeft S) HL g hOld
  · exact girthGT_injectedEdgeFamily (twoCopyPortRight S) HR g hNew

end StructuralRamsey.Girth
