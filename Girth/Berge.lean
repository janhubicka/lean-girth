import Girth.Support

/-! # Berge cycles and support girth

Instead of adjoining an infinity value, the formalization uses the proposition
`GirthGT H g`: the hypergraph `H` has no Berge cycle of length at most
`g`.  This is exactly the form used by the main theorem.
-/

namespace StructuralRamsey.Girth

universe u v
variable {W : Type v}

/-- Cyclic successor on a nonempty finite index type. -/
def cyclicSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.2)⟩

/-- A Berge cycle with distinct edges and distinct connecting vertices. -/
structure BergeCycle (H : Set (Set W)) where
  length : ℕ
  hlength : 2 ≤ length
  edge : Fin length → Set W
  vertex : Fin length → W
  edge_mem : ∀ i, edge i ∈ H
  edge_injective : Function.Injective edge
  vertex_injective : Function.Injective vertex
  left_mem : ∀ i, vertex i ∈ edge i
  right_mem : ∀ i, vertex i ∈ edge (cyclicSucc i)

namespace BergeCycle

/-- Reinterpret a Berge cycle in any hypergraph containing all of its edges. -/
def ofEdgeMem {H K : Set (Set W)} (c : BergeCycle H)
    (h : ∀ i, c.edge i ∈ K) :
    BergeCycle K where
  length := c.length
  hlength := c.hlength
  edge := c.edge
  vertex := c.vertex
  edge_mem := h
  edge_injective := c.edge_injective
  vertex_injective := c.vertex_injective
  left_mem := c.left_mem
  right_mem := c.right_mem

end BergeCycle

/-- The hypergraph has a Berge cycle of length at most `g`. -/
def HasBergeCycleAtMost (H : Set (Set W)) (g : ℕ) : Prop :=
  ∃ c : BergeCycle H, c.length ≤ g

/-- Girth strictly greater than `g`, expressed without an infinity value. -/
def GirthGT (H : Set (Set W)) (g : ℕ) : Prop :=
  ¬ HasBergeCycleAtMost H g

theorem girthGT_mono {H : Set (Set W)} {g h : ℕ}
    (hgt : GirthGT H g) (hhg : h ≤ g) :
    GirthGT H h := by
  intro hc
  rcases hc with ⟨c, hc⟩
  exact hgt ⟨c, hc.trans hhg⟩

theorem girthGT_one (H : Set (Set W)) : GirthGT H 1 := by
  rintro ⟨c, hc⟩
  have hlen : 2 ≤ c.length := c.hlength
  omega

/-- Passing to a subhypergraph cannot decrease girth. -/
theorem girthGT_of_subset {H K : Set (Set W)} {g : ℕ}
    (hHK : H ⊆ K) (hK : GirthGT K g) :
    GirthGT H g := by
  rintro ⟨c, hc⟩
  let cK : BergeCycle K := {
    length := c.length
    hlength := c.hlength
    edge := c.edge
    vertex := c.vertex
    edge_mem := fun i => hHK (c.edge_mem i)
    edge_injective := c.edge_injective
    vertex_injective := c.vertex_injective
    left_mem := c.left_mem
    right_mem := c.right_mem
  }
  exact hK ⟨cK, hc⟩

/-- Hypergraph girth greater than two implies linearity. -/
theorem pairwise_subsingleton_of_girthGT_two
    {H : Set (Set W)} (hgt : GirthGT H 2) :
    ∀ ⦃E F : Set W⦄, E ∈ H → F ∈ H → E ≠ F →
      (E ∩ F).Subsingleton := by
  intro E F hE hF hEF
  intro x hx y hy
  by_contra hxy
  let c : BergeCycle H := {
    length := 2
    hlength := by omega
    edge := ![E, F]
    vertex := ![x, y]
    edge_mem := by
      intro i
      fin_cases i
      · exact hE
      · exact hF
    edge_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    vertex_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    left_mem := by
      intro i
      fin_cases i
      · exact hx.1
      · exact hy.2
    right_mem := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using hx.2
      · simpa [cyclicSucc] using hy.1
  }
  exact hgt ⟨c, by simp [c]⟩

/-- The manuscript's support-girth condition at level two implies
`A`-linearity of the ambient structure. -/
theorem aLinear_of_girthGT_two
    {L : RelLanguage.{u}} {U : Type v}
    (A : StructuralRamsey.RelStructure L U)
    (D : StructuralRamsey.RelStructure L W)
    (hgt : GirthGT (supportCopies A D) 2) :
    ALinear A D := by
  intro e f hne
  apply pairwise_subsingleton_of_girthGT_two hgt
  · exact ⟨e, rfl⟩
  · exact ⟨f, rfl⟩
  · simpa [SameCopy] using hne


/-- Support copies transported through an ambient embedding. -/
def mappedSupportCopies
    {L : RelLanguage.{u}} {U T S : Type v}
    (A : StructuralRamsey.RelStructure L U)
    (D : StructuralRamsey.RelStructure L T)
    (E : StructuralRamsey.RelStructure L S)
    (i : StructuralRamsey.RelStructure.Embedding D E) :
    Set (Set S) :=
  {X | ∃ a : StructuralRamsey.RelStructure.Embedding A D,
    X = copyCarrier (i.comp a)}

/-- A Berge cycle among transported support copies pulls back through the
ambient embedding. -/
theorem girthGT_mappedSupportCopies
    {L : RelLanguage.{u}} {U T S : Type v}
    (A : StructuralRamsey.RelStructure L U)
    (D : StructuralRamsey.RelStructure L T)
    (E : StructuralRamsey.RelStructure L S)
    (i : StructuralRamsey.RelStructure.Embedding D E)
    {g : ℕ}
    (hgt : GirthGT (supportCopies A D) g) :
    GirthGT (mappedSupportCopies A D E i) g := by
  intro hcyc
  rcases hcyc with ⟨c, hcLen⟩
  classical
  choose a ha using fun j => c.edge_mem j
  have ha' (j : Fin c.length) :
      c.edge j = copyCarrier (i.comp (a j)) := ha j
  let oldEdge : Fin c.length → Set T :=
    fun j => copyCarrier (a j)
  have hOldEdgeMem (j : Fin c.length) :
      oldEdge j ∈ supportCopies A D := by
    exact ⟨a j, rfl⟩
  have hOldEdgeInj : Function.Injective oldEdge := by
    intro j k hjk
    apply c.edge_injective
    rw [ha' j, ha' k]
    change copyCarrier (i.comp (a j)) = copyCarrier (i.comp (a k))
    apply sameCopy_comp
    exact hjk
  have hvExists (j : Fin c.length) :
      ∃ x : T, i x = c.vertex j := by
    have hv : c.vertex j ∈ copyCarrier (i.comp (a j)) := by
      rw [← ha' j]
      exact c.left_mem j
    rcases hv with ⟨u, hu⟩
    exact ⟨a j u, hu⟩
  let oldVertex : Fin c.length → T :=
    fun j => Classical.choose (hvExists j)
  have hOldVertexMap (j : Fin c.length) :
      i (oldVertex j) = c.vertex j :=
    Classical.choose_spec (hvExists j)
  have hOldVertexInj : Function.Injective oldVertex := by
    intro j k hjk
    apply c.vertex_injective
    calc
      c.vertex j = i (oldVertex j) := (hOldVertexMap j).symm
      _ = i (oldVertex k) := congrArg i hjk
      _ = c.vertex k := hOldVertexMap k
  have hLeft (j : Fin c.length) :
      oldVertex j ∈ oldEdge j := by
    have hv : i (oldVertex j) ∈ copyCarrier (i.comp (a j)) := by
      rw [hOldVertexMap j, ← ha' j]
      exact c.left_mem j
    rcases hv with ⟨u, hu⟩
    have : oldVertex j = a j u := by
      apply i.injective
      exact hu
    exact ⟨u, this⟩
  have hRight (j : Fin c.length) :
      oldVertex j ∈ oldEdge (cyclicSucc j) := by
    have hv :
        i (oldVertex j) ∈
          copyCarrier (i.comp (a (cyclicSucc j))) := by
      rw [hOldVertexMap j, ← ha' (cyclicSucc j)]
      exact c.right_mem j
    rcases hv with ⟨u, hu⟩
    have : oldVertex j = a (cyclicSucc j) u := by
      apply i.injective
      exact hu
    exact ⟨u, this⟩
  let oldCycle : BergeCycle (supportCopies A D) := {
    length := c.length
    hlength := c.hlength
    edge := oldEdge
    vertex := oldVertex
    edge_mem := hOldEdgeMem
    edge_injective := hOldEdgeInj
    vertex_injective := hOldVertexInj
    left_mem := hLeft
    right_mem := hRight
  }
  exact hgt ⟨oldCycle, hcLen⟩

end StructuralRamsey.Girth
