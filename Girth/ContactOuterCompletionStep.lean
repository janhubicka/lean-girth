import Girth.ContactOuterPicture

/-! The actual outer completion step. The occupied standards
are indexed by the image of the selected family, so the local
degree budget is the size of the ORIGINAL family, not the
number of all core copies. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B : Type v}
variable {D : ContactHypergraphData V E I} {T : ContactTrainData E 1}
    {base : B → Set X} [LinearOrder V] [LinearOrder X]
    {allowed : Fin 1 → Set X} {q : Fin 2 → ℕ}
    {P : ContactTrainPicture D T base allowed q} {b : B}

namespace ContactTrainPicture.Core
variable (C : P.Core b) (hne : Nonempty (P.projection.StripEdge b))

/-- Every intersection of two distinct standards can be covered
by a designated old copy in either standard. In the edge case
use the actual shared edge label; in the singleton case use
vertex coverage. -/
theorem separator_covered
    (hP : P.graph.CopyCovered) (hC : C.graph.bottomCut.ZeroPairwise)
    (i j : C.Copy) (hne' : i ≠ j) :
    ∃ k : P.Copy,
      Set.range ((C.gluing hne).stdV i) ∩ Set.range ((C.gluing hne).stdV j) ⊆
        (C.gluing hne).stdV i '' P.graph.copyCarrier k := by
  let A := C.gluing hne
  have hne'' : (Sum.inl i : C.Copy ⊕ C.Edge) ≠ Sum.inl j :=
    fun he => hne' (Sum.inl.inj he)
  rcases A.owner_separator hC (Sum.inl i) (Sum.inl j) hne'' with hs | ⟨e,he,hi,hj⟩
  · by_cases h : (Set.range (A.stdV i) ∩ Set.range (A.stdV j)).Nonempty
    · obtain ⟨x,hx⟩ := h
      obtain ⟨v,hv⟩ := hx.1
      obtain ⟨k,hk⟩ := hP.1 v
      refine ⟨k,?_⟩
      intro y hy
      have hyx : y = x := hs hy hx
      exact ⟨v,hk,hv.trans hyx.symm⟩
    · obtain ⟨k,hk⟩ := hP.2 (Classical.choice hne).val
      exact ⟨k,fun y hy => (h ⟨y,hy⟩).elim⟩
  · obtain ⟨f,hf⟩ := (A.edge_domain i e).mpr hi
    obtain ⟨k,hk⟩ := hP.2 f
    refine ⟨k,?_⟩
    intro x hx
    have hmem : x ∈ A.coreV '' C.graph.edgeCarrier e := he ▸ hx
    have hEq := A.shared_edge_carrier i f e hf
    change (A.stdV i '' P.graph.edgeCarrier f) = (A.coreV '' C.graph.edgeCarrier e) at hEq
    rw [← hEq] at hmem
    obtain ⟨u,hu,hr⟩ := hmem
    exact ⟨u,P.projection.copy_edge_subset k f hk hu,hr⟩

/-- Preservation of qualitative completion for the *actual* new
designated family. No completion hypothesis on the output is
used to construct the core or to lift the join tree. -/
theorem next_completable
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < 1 → 2 ≤ q μ)
    (m : ℕ) (hm : 2 ≤ m)
    (hP : P.graph.CopyCovered)
    (hOld : ContactCompletable P.graph.copyCarrier m)
    (hC : C.graph.bottomCut.ZeroSmallMixedForestsThrough m) :
    ContactCompletable (C.next hne hbase hq).graph.copyCarrier m := by
  classical
  intro s hs hc
  let A := C.gluing hne
  let N := {p : C.Copy × P.Copy // p ∈ s}
  let owners : Finset C.Copy := s.image Prod.fst
  let Q := {i : C.Copy // i ∈ owners}
  letI : Fintype N := by
    change Fintype {p : C.Copy × P.Copy // p ∈ s}
    infer_instance
  letI : Fintype Q := by
    change Fintype {i : C.Copy // i ∈ owners}
    infer_instance
  letI : Nonempty N := by obtain ⟨n,hn⟩ := hs; exact ⟨⟨n,hn⟩⟩
  let owner (n : N) : Q :=
    ⟨n.val.1,Finset.mem_image.mpr ⟨n.val,n.property,rfl⟩⟩
  have hsurj : Function.Surjective owner := by
    intro i
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp i.property
    exact ⟨⟨n,hn⟩,Subtype.ext he⟩
  letI : Nonempty Q := ⟨owner (Classical.choice (inferInstance : Nonempty N))⟩
  letI : Finite P.Copy := P.finiteC
  letI : Fintype P.Copy := Fintype.ofFinite _
  let t₀ : Finset (C.Copy ⊕ C.Edge) := owners.image Sum.inl
  have ht₀ : t₀.Nonempty := by
    let i : Q := Classical.choice inferInstance
    exact ⟨Sum.inl i.val,Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
  have htcard : t₀.card ≤ m := by
    calc
      t₀.card ≤ owners.card := Finset.card_image_le
      _ ≤ s.card := Finset.card_image_le
      _ ≤ m := hc
  obtain ⟨J₀⟩ := hC.2 t₀ ht₀ htcard
  let f (i : Q) : {a : C.Copy ⊕ C.Edge // a ∈ t₀} :=
    ⟨Sum.inl i.val,Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val he))
  have hfs : Function.Surjective f := by
    intro a
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp a.property
    exact ⟨⟨i,hi⟩,Subtype.ext he⟩
  let r := Equiv.ofBijective f ⟨hf,hfs⟩
  let J₁ := J₀.reindex r
  let emb : Q ↪ C.Copy ⊕ C.Edge :=
    ⟨fun i => Sum.inl i.val,fun i j he => Subtype.ext (Sum.inl.inj he)⟩
  let J₂ : ContactJoinTree (fun i : Q => Set.range (A.stdV i.val)) :=
    A.owner_joinTree emb J₁
  let pieces (i : Q) (k : P.Copy) : Set A.Vertex := A.stdV i.val '' P.graph.copyCarrier k
  have hcontain (i : Q) (k : P.Copy) :
      pieces i k ⊆ Set.range (A.stdV i.val) := by
    rintro x ⟨v,_,rfl⟩
    exact ⟨v,rfl⟩
  have hsep (i : Q) (j : J₂.tree.neighborSet i) :
      ∃ k : P.Copy, Set.range (A.stdV i.val) ∩ Set.range (A.stdV j.val.val) ⊆ pieces i k :=
    C.separator_covered hne hP (hC.1 hm) i.val j.val.val
      (fun he => j.property.ne (Subtype.ext he))
  choose connector hconnector using hsep
  have hlocal (i : Q) : ContactCompletable (pieces i) m := by
    intro u hu huc
    obtain ⟨v,huv,⟨J⟩⟩ := hOld u hu huc
    exact ⟨v,huv,⟨J.mapVertices (A.stdV i.val)⟩⟩
  have hNcard : Fintype.card N ≤ m := by simpa [N] using hc
  obtain ⟨t,ht,hct,⟨J⟩⟩ := contact_qualitative_completion_lift
    (K := fun _ : Q => P.Copy) m hNcard owner hsurj
    (fun i => Set.range (A.stdV i.val)) J₂ pieces
    (fun n => n.val.2) connector hcontain
    (fun i j hadj => hconnector i ⟨j,hadj⟩) hlocal
  let L := Sigma (fun i : Q => {k : P.Copy // k ∈ t i})
  letI : Fintype L := by
    change Fintype (Sigma (fun i : Q => {k : P.Copy // k ∈ t i}))
    infer_instance
  let p (z : L) : C.Copy × P.Copy := (z.1.val,z.2.val)
  have hp : Function.Injective p := by
    rintro ⟨i,x⟩ ⟨j,y⟩ he
    have hij : i = j := Subtype.ext (congrArg Prod.fst he)
    subst j
    have hxy : x = y := Subtype.ext (congrArg Prod.snd he)
    subst y
    rfl
  let u : Finset (C.Copy × P.Copy) := Finset.univ.image p
  have hsu : s ⊆ u := by
    intro z hz
    let n : N := ⟨z,hz⟩
    exact Finset.mem_image.mpr ⟨⟨owner n,⟨z.2,ht n⟩⟩,Finset.mem_univ _,rfl⟩
  let p' (z : L) : {x // x ∈ u} :=
    ⟨p z,Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩⟩
  have hpi : Function.Injective p' := fun x y he => hp (congrArg Subtype.val he)
  have hps : Function.Surjective p' := by
    intro z
    obtain ⟨a,_,he⟩ := Finset.mem_image.mp z.property
    exact ⟨a,Subtype.ext he⟩
  let er := Equiv.ofBijective p' ⟨hpi,hps⟩
  have hEq : (fun x : {z // z ∈ u} => pieces (er.symm x).1 (er.symm x).2.val) =
      (fun x : {z // z ∈ u} => (C.next hne hbase hq).graph.copyCarrier x.val) := by
    funext x
    obtain ⟨z,rfl⟩ := er.surjective x
    rw [er.symm_apply_apply]
    rfl
  exact ⟨u,hsu,⟨hEq ▸ J.reindex er.symm⟩⟩

/-- All the outer invariants are preserved in the same step that
provides the colour-focusing embedding. -/
theorem next_outerInvariant
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < 1 → 2 ≤ q μ)
    (m : ℕ) (hm : 2 ≤ m) (hP : P.OuterInvariant m)
    (hCover : C.graph.CopyCovered)
    (hF : C.graph.bottomCut.ZeroSmallMixedForestsThrough m) :
    (C.next hne hbase hq).OuterInvariant m :=
  ⟨C.next_copyCovered hne hbase hq hP.1 hCover,
    C.next_pairwise hne hbase hq hP.2.1,
    C.next_completable hne hbase hq m hm hP.1 hP.2.2 hF⟩

end ContactTrainPicture.Core
end StructuralRamsey.Girth
