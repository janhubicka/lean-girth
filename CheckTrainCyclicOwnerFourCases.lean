import Girth.TrainCyclicOwnerFourCases

#print axioms StructuralRamsey.Girth.cyclicOwnerCut_four_cases
#print axioms StructuralRamsey.Girth.cyclicOwnerCut_four_cases_of_mem

-- A concrete cyclic standard-to-core boundary.
example :
    (∃ (i : Nat) (b : Nat),
      (fun j : Fin 3 =>
        if j = 0 then (Sum.inl 0 : Nat ⊕ Nat) else Sum.inr 1)
        (0 : Fin 3) = Sum.inl i ∧
      (fun j : Fin 3 =>
        if j = 0 then (Sum.inl 0 : Nat ⊕ Nat) else Sum.inr 1)
        (StructuralRamsey.Girth.cyclicSucc (0 : Fin 3)) = Sum.inr b) := by
  exact ⟨0, 1, by decide, by decide⟩
