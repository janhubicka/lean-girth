import Girth.ContactJoinTreeLift
import Girth.ContactCompletionBudget

/-! The qualitative outer completion step. Unlike the inner
forest increment, the local family is allowed to add genuine
designated copies. The degree budget is spent on actual copies
covering each incident separator, and the lifted tree keeps
all the resulting local completions. -/

namespace StructuralRamsey.Girth
universe v
variable {V N Q : Type v} {K : Q → Type v}

/-- A local selection of at most m pieces can be enlarged inside
the designated family to a join tree. -/
def ContactCompletable (F : N → Set V) (m : ℕ) : Prop :=
  ∀ s : Finset N, s.Nonempty → s.card ≤ m →
    ∃ t : Finset N, s ⊆ t ∧
      Nonempty (ContactJoinTree (fun i : {i // i ∈ t} => F i.val))

/-- The selected local copies and one separator-covering copy per
neighbour use at most the original global selection budget.
Complete each of these actual finite sets and lift their join
trees. No property of the output family is an extra hypothesis. -/
theorem contact_qualitative_completion_lift
    [Fintype N] [Nonempty N] [Fintype Q] [Nonempty Q]
    [∀ i, Fintype (K i)]
    (m : ℕ) (hcard : Fintype.card N ≤ m)
    (owner : N → Q) (hsurj : Function.Surjective owner)
    (outer : Q → Set V) (J : ContactJoinTree outer)
    (pieces : (i : Q) → K i → Set V)
    (selected : (n : N) → K (owner n))
    (connector : (i : Q) → J.tree.neighborSet i → K i)
    (hContain : ∀ i k, pieces i k ⊆ outer i)
    (hConnector : ∀ i j : Q, ∀ h : J.tree.Adj i j,
      outer i ∩ outer j ⊆ pieces i (connector i ⟨j,h⟩))
    (hLocal : ∀ i, ContactCompletable (pieces i) m) :
    ∃ t : (i : Q) → Finset (K i),
      (∀ n, selected n ∈ t (owner n)) ∧
      (∀ i j, connector i j ∈ t i) ∧
      Nonempty (ContactJoinTree
        (fun z : Sigma (fun i => {k : K i // k ∈ t i}) => pieces z.1 z.2.val)) := by
  classical
  let sel (i : Q) (n : {n : N // owner n = i}) : K i :=
    n.property ▸ selected n.val
  let R (i : Q) := {n : N // owner n = i} ⊕ J.tree.neighborSet i
  letI : ∀ i, Fintype (R i) := fun i => inferInstanceAs
    (Fintype ({n : N // owner n = i} ⊕ J.tree.neighborSet i))
  let request (i : Q) : R i → K i := fun z =>
    match z with
    | .inl n => sel i n
    | .inr j => connector i j
  let s (i : Q) : Finset (K i) := (Finset.univ : Finset (R i)).image (request i)
  have hs (i : Q) : (s i).Nonempty := by
    obtain ⟨n,hn⟩ := hsurj i
    let z : R i := Sum.inl ⟨n,hn⟩
    exact ⟨request i z,Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩⟩
  have hc (i : Q) : (s i).card ≤ m := by
    calc
      (s i).card ≤ Fintype.card (R i) := by
        simpa only [s,Finset.card_univ] using
          (Finset.card_image_le (s := (Finset.univ : Finset (R i))) (f := request i))
      _ = Fintype.card {n : N // owner n = i} + J.tree.degree i := by
        change Fintype.card ({n : N // owner n = i} ⊕ J.tree.neighborSet i) = _
        rw [Fintype.card_sum,J.tree.card_neighborSet_eq_degree]
      _ ≤ Fintype.card N :=
        contact_ownerFiber_card_add_degree_le owner hsurj J.tree i
      _ ≤ m := hcard
  choose t ht hTrees using fun i => hLocal i (s i) (hs i) (hc i)
  have hsel (n : N) : selected n ∈ t (owner n) := by
    apply ht (owner n)
    let z : R (owner n) := Sum.inl ⟨n,rfl⟩
    exact Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩
  have hcon (i : Q) (j : J.tree.neighborSet i) : connector i j ∈ t i :=
    ht i (Finset.mem_image.mpr ⟨Sum.inr j,Finset.mem_univ _,rfl⟩)
  let L (i : Q) := {k : K i // k ∈ t i}
  letI : ∀ i, Fintype (L i) := fun i => inferInstanceAs
    (Fintype {k : K i // k ∈ t i})
  letI : ∀ i, Nonempty (L i) := by
    intro i
    obtain ⟨k,hk⟩ := hs i
    exact ⟨⟨k,ht i hk⟩⟩
  let localTree (i : Q) : ContactJoinTree (fun k : L i => pieces i k.val) :=
    Classical.choice (hTrees i)
  let bridge (i j : Q) : L i :=
    if h : J.tree.Adj i j then ⟨connector i ⟨j,h⟩,hcon i ⟨j,h⟩⟩
    else Classical.choice (inferInstance : Nonempty (L i))
  have hb : ∀ ⦃i j : Q⦄, J.tree.Adj i j →
      outer i ∩ outer j ⊆ pieces i (bridge i j).val := by
    intro i j h
    simp only [bridge,dif_pos h]
    exact hConnector i j h
  exact ⟨t,hsel,hcon,
    contact_joinTree_lift_local J localTree
      (fun i k => hContain i k.val) bridge hb⟩

end StructuralRamsey.Girth
