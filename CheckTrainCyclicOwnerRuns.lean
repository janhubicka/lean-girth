import Girth.TrainCyclicOwnerRuns

#print axioms StructuralRamsey.Girth.cyclicOwnerChanges_zero_iff_constant
#print axioms StructuralRamsey.Girth.mem_cyclicOwnerCutPositions_iff
#print axioms StructuralRamsey.Girth.cyclicOwnerCutPositions_card
#print axioms StructuralRamsey.Girth.exists_cyclicOwnerCut_of_pos
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_minimal_zero_iff_one_standard
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_minimal_has_cut_of_not_one_standard

-- Finite regression: no cuts for a constant geometric owner word.
example :
    StructuralRamsey.Girth.cyclicOwnerChanges
        (fun _ : Fin 4 => (7 : Nat)) = 0 := by
  exact (StructuralRamsey.Girth.cyclicOwnerChanges_zero_iff_constant
    (by decide) (fun _ : Fin 4 => (7 : Nat))).mpr
      ⟨7, by intro; rfl⟩

-- A changing cyclic word must contain a cut.
example :
    ∃ k : Fin 3,
      (fun i : Fin 3 => i.val) k ≠
        (fun i : Fin 3 => i.val)
          (StructuralRamsey.Girth.cyclicSucc k) := by
  refine ⟨0, ?_⟩
  decide
