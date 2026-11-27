import Girth.ContactIncrementPieces

/-! The concrete forest increment for the actual tagged output
over a linear base. All selected owners and local labels are
constructed from the output; the core family is exactly the image
of the selected owner map. This invokes the previously constructed
join-tree increment, with no assumed local completion or output
forest property. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ X B : Type v}

namespace ContactTrainStrip
variable {m : ℕ} {D : ContactHypergraphData V E I} {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E m} {S : ContactTrainData E₀ m}
    (A : ContactTrainStrip D L T S)

theorem local_joinTree {q : ℕ} (hL : L.bottomCut.ZeroJoinTreesThrough q)
    (a : I ⊕ E) (s : Finset (A.localIndex a)) (hs : s.Nonempty) (hc : s.card ≤ q) :
    Nonempty (ContactJoinTree (fun j : {j // j ∈ s} => A.localPiece a j.val)) := by
  cases a with
  | inl i =>
    obtain ⟨J⟩ := hL s hs hc
    exact ⟨J.mapVertices (A.stdV i)⟩
  | inr e =>
    let J := {j : A.localIndex (Sum.inr e) // j ∈ s}
    letI : Nonempty J := by obtain ⟨j,hj⟩ := hs; exact ⟨⟨j,hj⟩⟩
    letI : Subsingleton J := ⟨fun j k => Subtype.ext (@Subsingleton.elim PUnit.{v+1} inferInstance j.val k.val)⟩
    exact ⟨ContactJoinTree.of_subsingleton (fun j : J => A.localPiece (Sum.inr e) j.val)⟩

/-- A core edge meets an output piece either in at most one vertex
or is entirely contained in it, as a consequence of the actual
trace geometry and core linearity. -/
theorem output_trace_strong {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (hA : A.ActiveOver P b)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (a : (I × I₀) ⊕ A.Edge) (e : E)
    (hn : ((A.coreV '' D.edgeCarrier e) ∩ A.outputHypergraph.bottomCut.carrier a).Nontrivial) :
    A.coreV '' D.edgeCarrier e ⊆ A.outputHypergraph.bottomCut.carrier a := by
  let K := A.outputHypergraph.bottomCut.carrier a
  let edge : E → Set A.Vertex := fun f => A.coreV '' D.edgeCarrier f
  have hcore : edge e ⊆ A.coreSet := by
    rintro x ⟨y,_,rfl⟩
    exact ⟨y,rfl⟩
  have ht : (K ∩ A.coreSet).Subsingleton ∨ ∃ f, K ∩ A.coreSet = edge f := by
    rcases A.output_piece_trace P b hA hbase a with hs | ⟨f,_,hf⟩
    · exact Or.inl hs
    · exact Or.inr ⟨f,hf⟩
  have hn' : (edge e ∩ (K ∩ A.coreSet)).Nontrivial := by
    obtain ⟨x,hx,y,hy,hxy⟩ := hn
    exact ⟨x,⟨hx.1,hx.2,hcore hx.1⟩,y,⟨hy.1,hy.2,hcore hy.1⟩,hxy⟩
  exact (contact_edgeTrace_strong edge (A.embedded_core_linear hlin) _ ht e hn').trans
    Set.inter_subset_left

/-- Direct forest increment on the actual output. The cutoff-one
case of the core property needs no global pairwise condition.
The input girth bound is only on the core's real edges. -/
theorem directIncrement [Fintype A.Vertex]
    {q : ℕ} (hq : 2 ≤ q)
    {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (hA : A.ActiveOver P b)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hg : LabelledGirthGT D.edgeCarrier q)
    (hD : D.bottomCut.ZeroSmallMixedForestsThrough (q-1))
    (hL : L.bottomCut.ZeroSmallMixedForestsThrough q) :
    A.outputHypergraph.bottomCut.ZeroSmallMixedForestsThrough q := by
  classical
  refine ⟨fun _ => A.output_pairwise_of_trace P b hA hbase hlin (hL.1 hq),?_⟩
  intro s hs hcard
  let N := {a // a ∈ s}
  letI : Nonempty N := by obtain ⟨a,ha⟩ := hs; exact ⟨⟨a,ha⟩⟩
  have hex : ∀ n : N, ∃ a : I ⊕ E, ∃ j : A.localIndex a,
      A.localOutputLabel a j = n.val := fun n => A.output_has_localLabel n.val
  choose own loc hlocalLabel using hex
  let used : Finset (I ⊕ E) := Finset.univ.image own
  let Q := {a // a ∈ used}
  have hused : used.Nonempty := by
    let n : N := Classical.choice inferInstance
    exact ⟨own n,Finset.mem_image.mpr ⟨n,Finset.mem_univ _,rfl⟩⟩
  letI : Nonempty Q := by obtain ⟨a,ha⟩ := hused; exact ⟨⟨a,ha⟩⟩
  let owner : N → Q := fun n =>
    ⟨own n,Finset.mem_image.mpr ⟨n,Finset.mem_univ _,rfl⟩⟩
  have hsurj : Function.Surjective owner := by
    intro a
    obtain ⟨n,_,hn⟩ := Finset.mem_image.mp a.property
    exact ⟨n,Subtype.ext hn⟩
  have hN : Fintype.card N ≤ q := by simpa [N] using hcard
  have hpair (hsmall : Fintype.card Q ≤ q-1) (a c : Q) (hne : a ≠ c) :
      D.bottomCut.ZeroPairwise := by
    have hval : a.val ≠ c.val := fun he => hne (Subtype.ext he)
    have hsub : ({a.val,c.val} : Finset (I ⊕ E)) ⊆ used := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact a.property
      · exact c.property
    have hh := Finset.card_le_card hsub
    rw [Finset.card_pair hval] at hh
    have hQ : Fintype.card Q = used.card := by simp [Q]
    exact hD.1 (by omega)
  let F : N → Set A.Vertex := fun n => A.outputHypergraph.bottomCut.carrier n.val
  let K : Q → Set A.Vertex := fun a => A.ownerPiece a.val
  let G : (a : Q) → A.localIndex a.val → Set A.Vertex := fun a j => A.localPiece a.val j
  let edge : E → Set A.Vertex := fun e => A.coreV '' D.edgeCarrier e
  have hcontain : ∀ n, F n ⊆ K (owner n) := by
    intro n
    have h := A.localOutput_carrier (own n) (loc n)
    rw [hlocalLabel n] at h
    change F n = A.localPiece (own n) (loc n) at h
    rw [h]
    exact A.localPiece_subset_owner _ _
  have hcross : ∀ a c : Q, a ≠ c → K a ∩ K c ⊆ A.coreSet :=
    fun a c hn => A.owner_cross a.val c.val (fun he => hn (Subtype.ext he))
  have htrace : ContactEdgeTraces edge (fun n => F n ∩ A.coreSet) := by
    intro n
    rcases A.output_piece_trace P b hA hbase n.val with hs | ⟨e,_,he⟩
    · exact Or.inl hs
    · exact Or.inr ⟨e,he⟩
  have hstrong : ∀ n e, (edge e ∩ F n).Nontrivial → edge e ⊆ F n :=
    fun n e hn => A.output_trace_strong P b hA hbase hlin n.val e hn
  have hsep : Fintype.card Q ≤ q-1 → ∀ a c : Q, a ≠ c →
      (K a ∩ K c).Subsingleton ∨ ∃ e, K a ∩ K c = edge e := by
    intro hsmall a c hn
    rcases A.owner_separator (hpair hsmall a c hn) a.val c.val
      (fun he => hn (Subtype.ext he)) with hs | ⟨e,he,_,_⟩
    · exact Or.inl hs
    · exact Or.inr ⟨e,he⟩
  have hlocalSel : ∀ n, ∃ j : A.localIndex (owner n).val, F n = G (owner n) j := by
    intro n
    refine ⟨loc n,?_⟩
    have h := A.localOutput_carrier (own n) (loc n)
    rw [hlocalLabel n] at h
    exact h
  have hlocalSep : Fintype.card Q ≤ q-1 → ∀ a c : Q, a ≠ c →
      ¬ (K a ∩ K c).Subsingleton → ∃ j : A.localIndex a.val, K a ∩ K c = G a j := by
    intro hsmall a c hn hnot
    rcases A.owner_separator (hpair hsmall a c hn) a.val c.val
      (fun he => hn (Subtype.ext he)) with hs | ⟨e,he,ha,_⟩
    · exact (hnot hs).elim
    · obtain ⟨j,hj⟩ := A.local_core_edge a.val e ha
      exact ⟨j,he.trans hj.symm⟩
  have houter : Fintype.card Q ≤ q-1 → Nonempty (ContactJoinTree K) := by
    intro hsmall
    have hc : used.card ≤ q-1 := by simpa [Q] using hsmall
    obtain ⟨J⟩ := hD.2 used hused hc
    exact ⟨A.owner_joinTree ⟨Subtype.val,Subtype.val_injective⟩ J⟩
  exact contact_directIncrement_joinTree edge F K G A.coreSet owner hsurj q hN
    (A.embedded_core_linear hlin) (A.embedded_core_girth hg)
    hcontain hcross htrace hstrong hsep hlocalSel hlocalSep
    (fun a s hs hc => A.local_joinTree hL.2 a.val s hs hc) houter

end ContactTrainStrip
end StructuralRamsey.Girth
