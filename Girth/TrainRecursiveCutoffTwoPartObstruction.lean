import Girth.TrainRecursiveUniformAllInputs

set_option autoImplicit false
set_option Elab.async false

/-!
# Why the cutoff-two shorter train is not automatically X-partite

The shorter-train filling uses one ordered edge template X and a canonical
parameterisation of each new X-edge. The new edges can share vertices that
are images of DIFFERENT X-coordinates, because two original first wagons
can meet in one vertex even though their copies inside the disjoint union
W are distinct. No global X-valued part map can preserve both
parameterisations in this situation.

This small negative lemma is independent of girth, colourings and Ramsey
theorems; it rules out the naive application of the partite order
assertion to an arbitrarily glued shorter train.

It does not construct a nonpartite RR witness. The correct cutoff-two
inductive input must be a same-vector, NONPARTITE order theorem on the
actual shorter train, or a separately proved faithful partite replacement.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe v
variable {X Y : Type v}

/-- Two canonical X-edge charts which identify distinct X-coordinates
cannot both preserve the same global X-part map. This is the formal
obstruction to identifying the all-input PARTITE order statement with
the unrestricted order statement at cutoff two. -/
theorem no_global_X_part_of_colliding_canonical_edges
    (βp βq : X → Y)
    (xp xq : X) (hDistinct : xp ≠ xq)
    (hGlue : βp xp = βq xq) :
    ¬ ∃ part : Y → X,
        (∀ x : X, part (βp x) = x) ∧
        (∀ x : X, part (βq x) = x) := by
  rintro ⟨part, hp, hq⟩
  apply hDistinct
  calc
    xp = part (βp xp) := (hp xp).symm
    _ = part (βq xq) := congrArg part hGlue
    _ = xq := hq xq

end StructuralRamsey.Girth.TrainRecursiveWitness
