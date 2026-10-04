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
  obtain ⟨r, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  letI : NeZero c.length := ⟨by omega⟩
  let cast : Fin (r + 1) → Fin c.length :=
    fun m => Fin.castLE (Nat.le_of_lt hklt) m
  let idx : Fin (r + 1) → Fin c.length :=
    fun m => cyclicRunIndex before (cast m)
  have hidx : Function.Injective idx := by
    intro i j hij
    let start : Fin c.length := finRotate c.length before
    have hc : cast i = cast j := by
      apply (finCycle start).injective
      simpa [idx, cast, cyclicRunIndex, start, finCycle_apply, add_comm] using hij
    exact Fin.castLE_injective (Nat.le_of_lt hklt) hc
  have hidx0 : idx 0 = cyclicSucc before := by
    rw [cyclicSucc_eq_finRotate]
    simp [idx, cast, cyclicRunIndex]
  have hidxSucc :
      ∀ {m : ℕ} (hm : m + 1 < r + 1),
        idx ⟨m + 1, hm⟩ = cyclicSucc (idx ⟨m, by omega⟩) := by
    intro m hm
    rw [cyclicSucc_eq_finRotate]
    apply Fin.ext
    simp [idx, cast, cyclicRunIndex, finCycle_apply, finRotate_apply,
      Fin.add_def, Nat.add_mod]
    omega
  let edges : Fin (r + 1) → Set W := fun m => c.edge (idx m)
  let vertices : Fin (r + 2) → W :=
    Fin.cons (c.vertex before) (fun m : Fin (r + 1) => c.vertex (idx m))
  have hedges : Function.Injective edges :=
    c.edge_injective.comp hidx
  have htail :
      Function.Injective (fun m : Fin (r + 1) => c.vertex (idx m)) :=
    c.vertex_injective.comp hidx
  have hhead :
      c.vertex before ∉
        Set.range (fun m : Fin (r + 1) => c.vertex (idx m)) := by
    rintro ⟨m, hm⟩
    have hbm : before = idx m := c.vertex_injective hm.symm
    have hform : idx m = before + (cast m + 1) := by
      rw [idx, cyclicRunIndex, finCycle_apply, finRotate_apply]
      ac_rfl
    rw [hform] at hbm
    have hzero : (cast m + 1 : Fin c.length) = 0 := by
      apply add_left_cancel (a := before)
      simpa using hbm.symm
    have haddlt : (cast m : ℕ) + 1 < c.length := by
      change (m : ℕ) + 1 < c.length
      omega
    have hval :
        ((cast m + 1 : Fin c.length) : ℕ) = (m : ℕ) + 1 := by
      simpa [cast] using
        (Fin.val_add_eq_of_add_lt haddlt :
          ((cast m + 1 : Fin c.length) : ℕ) =
            (cast m : ℕ) + 1)
    have hz := congrArg Fin.val hzero
    rw [hval] at hz
    simp at hz
  have hvertices : Function.Injective vertices := by
    exact Fin.cons_injective_iff.mpr ⟨hhead, htail⟩
  refine {
    length := r + 1
    hlength := by omega
    edge := edges
    vertex := vertices
    edge_mem := fun i => c.edge_mem (idx i)
    edge_injective := hedges
    vertex_injective := hvertices
    left_mem := ?_
    right_mem := ?_
  }
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [edges, vertices, hidx0] using c.right_mem before
    · have hs := hidxSucc (m := j.1) (by omega)
      have hm := c.right_mem (idx j.castSucc)
      simpa [edges, vertices, hs, Fin.succ_castSucc] using hm
  · intro i
    simpa [edges, vertices] using c.left_mem (idx i)

@[simp]
theorem cyclicPath_edge
    {H : Set (Set W)} (c : BergeCycle H)
    (before : Fin c.length) (k : ℕ)
    (hkpos : 0 < k) (hklt : k < c.length) (i : Fin k) :
    (c.cyclicPath before k hkpos hklt).edge i =
      c.edge (cyclicRunIndex before
        (Fin.castLE (Nat.le_of_lt hklt) i)) := by
  rfl

@[simp]
theorem cyclicPath_vertex_zero
    {H : Set (Set W)} (c : BergeCycle H)
    (before : Fin c.length) (k : ℕ)
    (hkpos : 0 < k) (hklt : k < c.length) :
    (c.cyclicPath before k hkpos hklt).vertex 0 =
      c.vertex before := by
  rfl

@[simp]
theorem cyclicPath_vertex_succ
    {H : Set (Set W)} (c : BergeCycle H)
    (before : Fin c.length) (k : ℕ)
    (hkpos : 0 < k) (hklt : k < c.length) (i : Fin k) :
    (c.cyclicPath before k hkpos hklt).vertex i.succ =
      c.vertex (cyclicRunIndex before
        (Fin.castLE (Nat.le_of_lt hklt) i)) := by
  rfl

@[simp]
theorem cyclicPath_vertex_last
    {H : Set (Set W)} (c : BergeCycle H)
    (before : Fin c.length) (k : ℕ)
    (hkpos : 0 < k) (hklt : k < c.length) :
    (c.cyclicPath before k hkpos hklt).vertex (Fin.last k) =
      c.vertex (before + (⟨k, hklt⟩ : Fin c.length)) := by
  letI : NeZero c.length := ⟨by omega⟩
  let off : Fin k := ⟨k - 1, by omega⟩
  let offN : Fin c.length :=
    Fin.castLE (Nat.le_of_lt hklt) off
  let kN : Fin c.length := ⟨k, hklt⟩
  have hlast : off.succ = Fin.last k := by
    apply Fin.ext
    simp [off]
    omega
  have haddlt : (offN : ℕ) + 1 < c.length := by
    change k - 1 + 1 < c.length
    omega
  have hoff : offN + 1 = kN := by
    apply Fin.ext
    have hv :
        ((offN + 1 : Fin c.length) : ℕ) =
          (offN : ℕ) + 1 :=
      Fin.val_add_eq_of_add_lt haddlt
    rw [hv]
    change k - 1 + 1 = k
    omega
  have hidx :
      cyclicRunIndex before offN = before + kN := by
    rw [cyclicRunIndex, finCycle_apply, finRotate_apply]
    calc
      before + 1 + offN = before + (offN + 1) := by ac_rfl
      _ = before + kN := by rw [hoff]
  rw [← hlast]
  rw [c.cyclicPath_vertex_succ before k hkpos hklt off]
  exact congrArg c.vertex hidx

end BergeCycle

end StructuralRamsey.Girth
