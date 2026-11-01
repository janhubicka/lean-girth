import Girth.TrainOneDoublePairedOwnerWord

/-!
# Pull an admissible paired long word back to output Fin indices

The literal paired owner certificate from the genuine n-to-n+1 long
replacement contains every old label-owner pair unchanged and two new
physical labels with the same receiving owner. This file removes a
remaining indexing ambiguity: a paired List whose label projection
is exactly the output List.ofFn gives a FIN-INDEXED owner assignment
on that output, with every occurrence individually admissible.

Crucially, the proof uses List.ofFn_get and List.ofFn_inj rather than
converting the reduced supreme standard into an original B-label.

What remains is nonincrease of CYCLIC owner cuts under duplication
and the concrete selected-picture source-to-output geometric
instantiation. No full cycle transfer is claimed; no appendix.
-/

namespace StructuralRamsey.Girth

universe v w
variable {Label : Type v} {Owner : Type w}

/-- An exact paired word for a Fin-indexed output label sequence
gives a genuine output owner function. No finite type assumption
on possible owners and no unproved source/target indices. -/
theorem finOwnerChoice_of_paired_word
    {m : ℕ} (outLabels : Fin m → Label)
    (paired : List (Label × Owner))
    (Allowed : Label → Owner → Prop)
    (hLength : paired.length = m)
    (hLabels : paired.map Prod.fst = List.ofFn outLabels)
    (hAllowed : ∀ z ∈ paired, Allowed z.1 z.2) :
    ∃ newOwner : Fin m → Owner,
      ∀ k : Fin m, Allowed (outLabels k) (newOwner k) := by
  let pairAt : Fin m → Label × Owner :=
    fun k => paired.get (Fin.cast hLength.symm k)
  have hPaired : List.ofFn pairAt = paired := by
    calc
      List.ofFn pairAt =
          List.ofFn (fun k : Fin m =>
            paired.get (Fin.cast hLength.symm k)) := rfl
      _ = List.ofFn (List.get paired) :=
            (List.ofFn_congr hLength (List.get paired)).symm
      _ = paired := List.ofFn_get paired
  have hLabelList :
      List.ofFn (fun k : Fin m => (pairAt k).1) =
        List.ofFn outLabels := by
    calc
      List.ofFn (fun k : Fin m => (pairAt k).1) =
          (List.ofFn pairAt).map Prod.fst := by
            simp [List.map_ofFn] <;> (funext t; rfl)
      _ = paired.map Prod.fst :=
            congrArg (List.map Prod.fst) hPaired
      _ = List.ofFn outLabels := hLabels
  have hLabelAt :
      ∀ k : Fin m, (pairAt k).1 = outLabels k :=
    fun k => congrFun (List.ofFn_inj.mp hLabelList) k
  refine ⟨fun k => (pairAt k).2, ?_⟩
  intro k
  have hkMem : pairAt k ∈ paired := by
    rw [← hPaired]
    exact List.mem_ofFn.mpr ⟨k, rfl⟩
  have h := hAllowed (pairAt k) hkMem
  change Allowed (outLabels k) (pairAt k).2
  rw [← hLabelAt k]
  exact h

/-- For a literal one-long label replacement, every old admissible
owner can be retained while both inserted physical edges receive
the SAME standard owner. This produces an actual output Fin-indexed
admissible assignment, not merely a list of candidate owners. -/
theorem oneDoubleWord_fin_owner_admissible
    {n m : ℕ} (labels : Fin n → Label)
    (oldOwner : Fin n → Owner)
    (j : Fin n) (first second : Label) (target : Owner)
    (outLabels : Fin m → Label)
    (Allowed : Label → Owner → Prop)
    (hOld : ∀ k : Fin n, Allowed (labels k) (oldOwner k))
    (hFirst : Allowed first target)
    (hSecond : Allowed second target)
    (hWord : List.ofFn outLabels =
      oneDoubleWord labels j first second) :
    ∃ newOwner : Fin m → Owner,
      ∀ k : Fin m, Allowed (outLabels k) (newOwner k) := by
  let paired := oneDoublePairedWord
    labels oldOwner j first second target
  have hLabelProjection :
      paired.map Prod.fst = List.ofFn outLabels :=
    (oneDoublePairedWord_label_projection
      labels oldOwner j first second target).trans hWord.symm
  have hLength : paired.length = m := by
    have hP := congrArg List.length hLabelProjection
    simp only [List.length_map, List.length_ofFn] at hP
    exact hP
  have hAdmissible : ∀ z ∈ paired, Allowed z.1 z.2 :=
    oneDoublePairedWord_admissible labels oldOwner j
      first second target Allowed hOld hFirst hSecond
  exact finOwnerChoice_of_paired_word
    outLabels paired Allowed hLength hLabelProjection hAdmissible

end StructuralRamsey.Girth
