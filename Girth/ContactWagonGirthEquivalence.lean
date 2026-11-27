import Girth.ContactParentMap
import Girth.ContactCycleCompression

/-! The manuscript's finer-cut projection and parent-by-parent wagon
girth equivalence. All families retain their wagon labels, including
different wagons with identical carriers. No finiteness, connectivity,
partite-parameter, or additional linearity hypothesis is needed. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I : Type v}

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)
variable {m : ℕ} (T : ContactTrainData E m)

/-- Quantitative projection from any finer wagon cut, rather than only
from the original edge cut. A nonconstant ancestor word would compress
to a short labelled Berge cycle in the coarser family. -/
theorem finer_cycle_constant_at_coarser_cut
    (μ ν : Fin (m+1)) (hμν : μ ≤ ν) {g : ℕ}
    (hg : LabelledGirthGT (D.atCut (T.parent ν)).contactWagonCarrier g)
    (C : LabelledBergeCycle (D.atCut (T.parent μ)).contactWagonCarrier)
    (hshort : C.length ≤ g) :
    ∀ i j, T.parentMap μ ν hμν (C.label i) = T.parentMap μ ν hμν (C.label j) := by
  classical
  let owner := fun i => T.parentMap μ ν hμν (C.label i)
  let K := (D.atCut (T.parent ν)).contactWagonCarrier
  have hContain : ∀ i,
      (D.atCut (T.parent μ)).contactWagonCarrier (C.label i) ⊆ K (owner i) :=
    fun i => D.wagon_parent_subset T μ ν hμν (C.label i)
  by_contra h
  have hnon : ¬ ∃ p, ∀ i, owner i = p := by
    rintro ⟨p,hp⟩
    exact h (fun i j => (hp i).trans (hp j).symm)
  have hchanges := C.contact_changes_gt owner K hContain hg hnon
  have hbound : contactOwnerChanges owner ≤ C.length := by
    rw [← contactOwnerCutPositions_card owner]
    simpa using Finset.card_le_card (Finset.subset_univ (contactOwnerCutPositions owner))
  omega

/-- Explicit containment of every fine member in the same actual
coarser wagon, with its ancestor identity retained. -/
theorem finer_cycle_in_one_coarser_wagon
    (μ ν : Fin (m+1)) (hμν : μ ≤ ν) {g : ℕ}
    (hg : LabelledGirthGT (D.atCut (T.parent ν)).contactWagonCarrier g)
    (C : LabelledBergeCycle (D.atCut (T.parent μ)).contactWagonCarrier)
    (hshort : C.length ≤ g) :
    ∃ p : T.Wagon ν, ∀ i,
      T.parentMap μ ν hμν (C.label i) = p ∧
      (D.atCut (T.parent μ)).contactWagonCarrier (C.label i) ⊆
        (D.atCut (T.parent ν)).contactWagonCarrier p := by
  let zero : Fin C.length := ⟨0,by have := C.hlength; omega⟩
  let p := T.parentMap μ ν hμν (C.label zero)
  have hc := D.finer_cycle_constant_at_coarser_cut T μ ν hμν hg C hshort
  refine ⟨p,fun i => ⟨hc i zero,?_⟩⟩
  dsimp only [p]
  rw [← hc i zero]
  exact D.wagon_parent_subset T μ ν hμν (C.label i)

/-- In the acyclic case no length restriction is required. Acyclicity
here literally means that the indexed coarser family has no Berge cycle. -/
theorem finer_cycle_in_one_coarser_wagon_of_acyclic
    (μ ν : Fin (m+1)) (hμν : μ ≤ ν)
    (hacyclic : ¬ Nonempty (LabelledBergeCycle
      (D.atCut (T.parent ν)).contactWagonCarrier))
    (C : LabelledBergeCycle (D.atCut (T.parent μ)).contactWagonCarrier) :
    ∃ p : T.Wagon ν, ∀ i,
      T.parentMap μ ν hμν (C.label i) = p ∧
      (D.atCut (T.parent μ)).contactWagonCarrier (C.label i) ⊆
        (D.atCut (T.parent ν)).contactWagonCarrier p :=
  D.finer_cycle_in_one_coarser_wagon T μ ν hμν
    (fun ⟨B,_⟩ => hacyclic ⟨B⟩) C le_rfl

/-- The child-cut family inside one actual coarser wagon. This is an
indexed restriction, so coincident carriers are never collapsed. -/
def parentChildCarrier (μ ν : Fin (m+1)) (hμν : μ ≤ ν) (p : T.Wagon ν) :
    {a : T.Wagon μ // T.parentMap μ ν hμν a = p} → Set V :=
  fun a => (D.atCut (T.parent μ)).contactWagonCarrier a.val

theorem parent_child_girth_of_global
    (μ ν : Fin (m+1)) (hμν : μ ≤ ν) {g : ℕ}
    (hg : LabelledGirthGT (D.atCut (T.parent μ)).contactWagonCarrier g)
    (p : T.Wagon ν) : LabelledGirthGT (D.parentChildCarrier T μ ν hμν p) g :=
  labelledGirthGT_of_injective_reindex _ Subtype.val Subtype.val_injective g hg

/-- Coarser global girth together with the girth of every child fibre
gives global girth at the finer cut. -/
theorem finer_girth_of_parent_and_children
    (μ ν : Fin (m+1)) (hμν : μ ≤ ν) {g : ℕ}
    (hparent : LabelledGirthGT (D.atCut (T.parent ν)).contactWagonCarrier g)
    (hchildren : ∀ p : T.Wagon ν,
      LabelledGirthGT (D.parentChildCarrier T μ ν hμν p) g) :
    LabelledGirthGT (D.atCut (T.parent μ)).contactWagonCarrier g := by
  rintro ⟨C,hshort⟩
  obtain ⟨p,hp⟩ := D.finer_cycle_in_one_coarser_wagon T μ ν hμν hparent C hshort
  let B : LabelledBergeCycle (D.parentChildCarrier T μ ν hμν p) := {
    length := C.length
    hlength := C.hlength
    label := fun i => ⟨C.label i,(hp i).1⟩
    vertex := C.vertex
    label_injective := fun _ _ h => C.label_injective (congrArg Subtype.val h)
    vertex_injective := C.vertex_injective
    left_mem := C.left_mem
    right_mem := C.right_mem }
  exact hchildren p ⟨B,hshort⟩

/-- The manuscript's vector has one coordinate for each proper cut:
q j is its bound g_(j+1), and the universal top has no coordinate. -/
def ProperWagonGirth (q : Fin m → ℕ) : Prop :=
  ∀ j, LabelledGirthGT (D.atCut (T.parent j.castSucc)).contactWagonCarrier (q j)

/-- The corresponding parent-by-parent bounds on immediate child wagons. -/
def ParentWagonGirth (q : Fin m → ℕ) : Prop :=
  ∀ (j : Fin m) (p : T.Wagon j.succ), LabelledGirthGT
    (D.parentChildCarrier T j.castSucc j.succ (by exact Nat.le_succ j.val) p) (q j)

/-- The parent-by-parent formulation is equivalent to global wagon
girth for a nondecreasing cutoff vector. The proof works even without
the manuscript's lower bound two on its entries. -/
theorem properWagonGirth_iff_parentWagonGirth
    (q : Fin m → ℕ) (hq : Monotone q) :
    D.ProperWagonGirth T q ↔ D.ParentWagonGirth T q := by
  constructor
  · intro h j p
    exact D.parent_child_girth_of_global T j.castSucc j.succ
      (by exact Nat.le_succ j.val) (h j) p
  · intro h
    have aux : ∀ d : ℕ, ∀ j : Fin m, m-j.val = d →
        LabelledGirthGT (D.atCut (T.parent j.castSucc)).contactWagonCarrier (q j) := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro j hj
        have hparent : LabelledGirthGT
            (D.atCut (T.parent j.succ)).contactWagonCarrier (q j) := by
          by_cases htop : j.val+1 = m
          · have he : j.succ = (⟨m,by omega⟩ : Fin (m+1)) := Fin.ext htop
            rw [he]
            exact D.top_wagonGirth T (q j)
          · let k : Fin m := ⟨j.val+1,by have := j.isLt; omega⟩
            have hlt : m-k.val < d := by
              dsimp [k]
              have := j.isLt
              omega
            have hnext := ih (m-k.val) hlt k rfl
            have hqjk : q j ≤ q k := hq (by change j.val ≤ j.val+1; omega)
            have hidx : k.castSucc = j.succ := Fin.ext rfl
            rw [← hidx]
            rintro ⟨B,hB⟩
            exact hnext ⟨B,hB.trans hqjk⟩
        exact D.finer_girth_of_parent_and_children T j.castSucc j.succ
          (by exact Nat.le_succ j.val) hparent (h j)
    exact fun j => aux (m-j.val) j rfl

end ContactHypergraphData
end StructuralRamsey.Girth
