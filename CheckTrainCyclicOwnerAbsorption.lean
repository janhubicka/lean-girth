import Girth.TrainCyclicOwnerAbsorption

#print axioms StructuralRamsey.Girth.cyclicSucc_ne_self_of_two_le
#print axioms StructuralRamsey.Girth.cyclicOwnerChanges_absorb_right
#print axioms StructuralRamsey.Girth.cyclicOwnerChanges_absorb_left
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_minimal_no_absorbable_core_right
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_minimal_no_absorbable_core_left

-- Two-occurrence wrap regression: absorbing the right neighbour
-- collapses both original cyclic cuts.
example :
    StructuralRamsey.Girth.cyclicOwnerChanges
      (StructuralRamsey.Girth.cyclicReplaceOwner
        (fun i : Fin 2 => i.val) (0 : Fin 2) 1) <
      StructuralRamsey.Girth.cyclicOwnerChanges
        (fun i : Fin 2 => i.val) := by
  apply StructuralRamsey.Girth.cyclicOwnerChanges_absorb_right
    (by decide) (fun i : Fin 2 => i.val) (0 : Fin 2) 1
  · decide
  · decide
  · decide
