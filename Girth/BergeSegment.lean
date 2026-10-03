import Girth.BergePath
import Girth.CyclicRun
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Cyclic segments of a Berge cycle

Any proper nonempty block of consecutive edges of a Berge cycle is a Berge
path.  This bridges the side-run selected in the cyclic-run lemma and the
path-closing construction in BergePath.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

namespace BergeCycle

/-- The next k edges after connector index before, for 0 < k < length,
form a Berge path of length k. -/
def cyclicPath
    {H : Set (Set W)} (c : BergeCycle H)
    (before : Fin c.length) (k : ℕ)
    (hkpos : 0 < k) (hklt : k < c.length) :
    BergePath H := by
  let start : Fin c.length := finRotate c.length before
  let cast : Fin k → Fin c.length :=
    fun m => Fin.castLE (Nat.le_of_lt hklt) m
  let idx : Fin k → Fin c.length :=
    fun m => finCycle start (cast m)
  have hidx : Function.Injective idx := by
    intro i j hij
    have hc : cast i = cast j := (finCycle start).injective hij
    apply Fin.ext
    exact congrArg Fin.val hc
  have hidx0 : idx 0 = cyclicSucc before := by
    rw [cyclicSucc_eq_finRotate]
    simp [idx, cast, start, finCycle_apply]
  have hidxSucc :
      ∀ {m : ℕ} (hm : m + 1 < k),
        idx ⟨m + 1, hm⟩ = cyclicSucc (idx ⟨m, by omega⟩) := by
    intro m hm
    rw [cyclicSucc_eq_finRotate]
    apply Fin.ext
    simp [idx, cast, start, finCycle_apply, finRotate_apply,
      Fin.add_def, Nat.add_mod]
    omega
  let edges : Fin k → Set W := fun m => c.edge (idx m)
  let vertices : Fin (k + 1) → W :=
    Fin.cons (c.vertex before) (fun m : Fin k => c.vertex (idx m))
  have hedges : Function.Injective edges :=
    c.edge_injective.comp hidx
  have htail :
      Function.Injective (fun m : Fin k => c.vertex (idx m)) :=
    c.vertex_injective.comp hidx
  have hhead :
      c.vertex before ∉
        Set.range (fun m : Fin k => c.vertex (idx m)) := by
    rintro ⟨m, hm⟩
    have hbm : before = idx m := c.vertex_injective hm.symm
    have hEq : before = before + (cast m + 1) := by
      simpa [idx, cast, start, finCycle_apply, finRotate_apply,
        add_assoc, add_comm, add_left_comm] using hbm
    have hzero : (cast m + 1 : Fin c.length) = 0 := by
      apply add_left_cancel (a := before)
      simpa using hEq.symm
    have haddlt : (cast m : ℕ) + 1 < c.length := by
      change (m : ℕ) + 1 < c.length
      omega
    have hval :
        ((cast m + 1 : Fin c.length) : ℕ) = (m : ℕ) + 1 :=
      Fin.val_add_eq_of_add_lt haddlt
    have hz := congrArg Fin.val hzero
    rw [hval] at hz
    simp at hz
  have hvertices : Function.Injective vertices := by
    exact Fin.cons_injective_iff.mpr ⟨hhead, htail⟩
  refine {
    length := k
    hlength := hkpos
    edge := edges
    vertex := vertices
    edge_mem := fun i => c.edge_mem (idx i)
    edge_injective := hedges
    vertex_injective := hvertices
    left_mem := ?_
    right_mem := ?_
  }
  · intro i
    cases i using Fin.cases with
    | zero =>
        simpa [edges, vertices, hidx0] using c.right_mem before
    | succ j =>
        have hs := hidxSucc (m := j.1) (by omega)
        have hm := c.right_mem (idx j.castSucc)
        simpa [edges, vertices, hs] using hm
  · intro i
    simpa [edges, vertices] using c.left_mem (idx i)

end BergeCycle

end StructuralRamsey.Girth
