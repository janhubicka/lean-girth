import Girth.TrainFillingRetainedRestriction

/-!
# Long-piece freshness across deleted filling wagons

Source A2 puts every vertex contact of a deleted wagon in its contracting
old edge. An OLD long piece cannot use that wagon. Absence from the
projected connector word therefore implies absence from the whole source.
No global filled replacement output is assumed.
-/
namespace StructuralRamsey.Girth.TrainFilling
universe v
variable {V I P : Type v}
variable (F : TrainFilling V) (copyCarrier : I → Set V)
variable (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P)
local notation "O" => F.oldData copyCarrier copyEdges parent
local notation "H" => F.filledData copyCarrier copyEdges parent

theorem deleted_wagon_contacts_in_old_edge
    {n : ℕ} (C : (H).BigCycle n) (hA2 : C.A2) (i : Fin n)
    (hi : F.ContractibleBlock copyCarrier copyEdges parent C i)
    (p : P) (hp : C.connector i = Sum.inr p) :
    ∃ f : F.OldEdge, ∀ (j : Fin n) (x : V),
      C.connector j = Sum.inl x → (H).WagonVertex p x → x ∈ f.1 := by
  obtain ⟨q, u, z, hq, hu, hz, _hDifferent, _hqu, _hqz, f, huf, hzf⟩ := hi
  have hqp : q = p := Sum.inr.inj (hq.symm.trans hp)
  subst q
  refine ⟨f, ?_⟩
  intro j x hx hpx
  rcases hA2.1 i p hp j ⟨x, hx, hpx⟩ with hj | hj
  · have hxu : x = u := by
      apply Sum.inl.inj
      exact hx.symm.trans (by rw [hj]; exact hu)
    rw [hxu]
    exact huf
  · have hxz : x = z := by
      apply Sum.inl.inj
      exact hx.symm.trans (by rw [hj]; exact hz)
    rw [hxz]
    exact hzf

theorem old_nonedge_wagon_not_deleted
    {n : ℕ} (C : (H).BigCycle n) (hA2 : C.A2)
    (p : P) (a b : Fin n) (x y : V)
    (hx : C.connector a = Sum.inl x)
    (hy : C.connector b = Sum.inl y)
    (hpx : (H).WagonVertex p x) (hpy : (H).WagonVertex p y)
    (hNoOld : ¬ (O).PairEdge x y) :
    ∀ i : Fin n, F.ContractibleBlock copyCarrier copyEdges parent C i →
      C.connector i ≠ Sum.inr p := by
  intro i hi hp
  obtain ⟨f, hf⟩ := F.deleted_wagon_contacts_in_old_edge
    copyCarrier copyEdges parent C hA2 i hi p hp
  exact hNoOld ⟨f, hf a x hx hpx, hf b y hy hpy⟩

theorem old_long_wagon_fresh_in_source
    {n : ℕ} (C : (H).BigCycle n)
    (B : (O).BigCycle (F.retainedPositions copyCarrier copyEdges parent C).card)
    (hA2 : C.A2)
    (hConnector : ∀ j,
      C.connector (F.retainedIndex copyCarrier copyEdges parent C j) = B.connector j)
    (p : P) (hAbsent : ∀ j, B.connector j ≠ Sum.inr p)
    (a b : Fin n) (x y : V)
    (hx : C.connector a = Sum.inl x)
    (hy : C.connector b = Sum.inl y)
    (hpx : (H).WagonVertex p x) (hpy : (H).WagonVertex p y)
    (hNoOld : ¬ (O).PairEdge x y) :
    ∀ i : Fin n, C.connector i ≠ Sum.inr p := by
  classical
  intro i hp
  by_cases hi : F.ContractibleBlock copyCarrier copyEdges parent C i
  · exact F.old_nonedge_wagon_not_deleted copyCarrier copyEdges parent
      C hA2 p a b x y hx hy hpx hpy hNoOld i hi hp
  · have hMem : i ∈ F.retainedPositions copyCarrier copyEdges parent C :=
      (F.retainedPositions_mem_iff copyCarrier copyEdges parent C i).mpr hi
    rw [← F.retainedIndex_image copyCarrier copyEdges parent C] at hMem
    obtain ⟨j, _hj, hji⟩ := Finset.mem_image.mp hMem
    apply hAbsent j
    exact (hConnector j).symm.trans (by rw [hji]; exact hp)
end StructuralRamsey.Girth.TrainFilling
