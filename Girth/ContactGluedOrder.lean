import Girth.ContactTaggedPicture
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! Compatible finite orders on the actual tagged free union.
Insert a private standard vertex just after its last shared
predecessor in the core. Within each insertion interval keep the
old standard order, and break ties between different standards
arbitrarily. This is an explicit order construction, so no
acyclicity or order-extension premise is needed. -/

namespace StructuralRamsey.Girth
universe v
variable {U V I : Type v}

/-- Finite rank in a linear order, with no chosen enumeration. -/
noncomputable def contactOrderRank {W : Type v} [Fintype W] [LinearOrder W]
    (x : W) : ℕ := (Finset.univ.filter (fun y : W => y < x)).card

theorem contactOrderRank_strict {W : Type v} [Fintype W] [LinearOrder W] :
    StrictMono (contactOrderRank : W → ℕ) := by
  classical
  intro x y hxy
  unfold contactOrderRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2.trans hxy⟩
  · intro he
    have hx : x ∈ Finset.univ.filter (fun z : W => z < y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy⟩
    rw [← he] at hx
    exact lt_irrefl x (Finset.mem_filter.mp hx).2

namespace ContactGluedOrder
variable [Fintype U] [Fintype V] [LinearOrder U] [LinearOrder V]
    (g : I → V → Option U)

def Compatible : Prop :=
  ∀ i x y u w, g i x = some u → g i y = some w → x < y → u < w

/-- A shared core vertex has positive rank, while an absent
predecessor contributes zero to the insertion slot. -/
noncomputable def value (i : I) (x : V) : ℕ :=
  (g i x).elim 0 (fun u => contactOrderRank u+1)

noncomputable def slot (i : I) (x : V) : ℕ :=
  (Finset.univ.filter (fun y : V => y ≤ x)).sup (value g i)

theorem slot_mono (i : I) : Monotone (slot g i) := by
  intro x y h
  apply Finset.sup_mono
  intro t ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ht).2.trans h⟩

/-- A shared vertex sits exactly at its own core rank. -/
theorem slot_shared (hc : Compatible g) (i : I) (x : V) (u : U)
    (hx : g i x = some u) :
    slot g i x = contactOrderRank u+1 := by
  classical
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro y hy
    have hyx := (Finset.mem_filter.mp hy).2
    cases h : g i y with
    | none => simp [value,h]
    | some w =>
      simp only [value,h,Option.elim]
      rcases lt_or_eq_of_le hyx with hlt | he
      · exact Nat.succ_le_succ (contactOrderRank_strict (hc i y x w u h hx hlt)).le
      · subst y
        rw [hx] at h
        have he := Option.some.inj h.symm
        rw [he]
  · have hmem : x ∈ Finset.univ.filter (fun y : V => y ≤ x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_rfl⟩
    have h := Finset.le_sup (f := value g i) hmem
    simpa only [value,hx,Option.elim] using h

/-- A predecessor of a shared vertex lies strictly before its
slot, even when it is itself private. -/
theorem slot_before_shared (hc : Compatible g) (i : I) (x y : V) (u : U)
    (hxy : x < y) (hy : g i y = some u) :
    slot g i x < contactOrderRank u+1 := by
  classical
  have hbound : slot g i x ≤ contactOrderRank u := by
    apply Finset.sup_le_iff.mpr
    intro z hz
    have hzy : z < y := ((Finset.mem_filter.mp hz).2).trans_lt hxy
    cases h : g i z with
    | none => simp [value,h]
    | some w =>
      have hh := contactOrderRank_strict (hc i z y w u h hy hzy)
      simp only [value,h,Option.elim]
      omega
  omega

/-- First coordinate is the insertion slot; second is zero for
a core point and the old rank plus one for a private point. -/
noncomputable def key (z : ContactGlued g) : ℕ ×ₗ ℕ :=
  match z.val with
  | .inl u => toLex (contactOrderRank u+1,0)
  | .inr (i,x) => toLex (slot g i x,contactOrderRank x+1)

theorem key_core (u : U) :
    key g (contactCoreEmb g u) = toLex (contactOrderRank u+1,0) := rfl

theorem key_std_shared
    (hinj : ∀ i x y u, g i x = some u → g i y = some u → x = y)
    (i : I) (x : V) (u : U) (hx : g i x = some u) :
    key g (contactStandardEmb g hinj i x) = toLex (contactOrderRank u+1,0) := by
  rw [(contactStandardEmb_eq_core g hinj i x u).mpr hx,key_core]

theorem key_std_private
    (hinj : ∀ i x y u, g i x = some u → g i y = some u → x = y)
    (i : I) (x : V) (hx : g i x = none) :
    key g (contactStandardEmb g hinj i x) = toLex (slot g i x,contactOrderRank x+1) := by
  change (match gluedStandardNode g i x with
    | .inl u => toLex (contactOrderRank u+1,0)
    | .inr (j,y) => toLex (slot g j y,contactOrderRank y+1)) = _
  simp only [gluedStandardNode,hx]

theorem key_core_strict : StrictMono (key g ∘ contactCoreEmb g) := by
  intro x y h
  change key g (contactCoreEmb g x) < key g (contactCoreEmb g y)
  rw [key_core,key_core]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (Nat.succ_lt_succ (contactOrderRank_strict h)))

theorem key_std_strict (hc : Compatible g)
    (hinj : ∀ i x y u, g i x = some u → g i y = some u → x = y)
    (i : I) : StrictMono (key g ∘ contactStandardEmb g hinj i) := by
  intro x y hxy
  change key g (contactStandardEmb g hinj i x) < key g (contactStandardEmb g hinj i y)
  have hmono := slot_mono g i hxy.le
  cases hy : g i y with
  | some w =>
    have hlt := slot_before_shared g hc i x y w hxy hy
    rw [key_std_shared g hinj i y w hy]
    cases hx : g i x with
    | some u =>
      rw [key_std_shared g hinj i x u hx]
      rw [slot_shared g hc i x u hx] at hlt
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
    | none =>
      rw [key_std_private g hinj i x hx]
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
  | none =>
    rw [key_std_private g hinj i y hy]
    cases hx : g i x with
    | some u =>
      rw [key_std_shared g hinj i x u hx]
      rw [slot_shared g hc i x u hx] at hmono
      apply Prod.Lex.toLex_lt_toLex'.mpr
      exact ⟨hmono,fun _ => Nat.succ_pos _⟩
    | none =>
      rw [key_std_private g hinj i x hx]
      apply Prod.Lex.toLex_lt_toLex'.mpr
      exact ⟨hmono,fun _ => Nat.succ_lt_succ (contactOrderRank_strict hxy)⟩

/-- The constructed order extends the core order and all standard
orders simultaneously. An injective finite tie-breaker is used
only between vertices that need no relative source ordering. -/
theorem exists_order [Finite I] (hc : Compatible g)
    (hinj : ∀ i x y u, g i x = some u → g i y = some u → x = y) :
    ∃ o : LinearOrder (ContactGlued g),
      (∀ x y : U, x < y → o.lt (contactCoreEmb g x) (contactCoreEmb g y)) ∧
      (∀ i (x y : V), x < y →
        o.lt (contactStandardEmb g hinj i x) (contactStandardEmb g hinj i y)) := by
  classical
  letI : Fintype (ContactGlued g) := Fintype.ofFinite _
  let tie := Fintype.equivFin (ContactGlued g)
  let f : ContactGlued g → (ℕ ×ₗ ℕ) ×ₗ Fin (Fintype.card (ContactGlued g)) :=
    fun z => toLex (key g z,tie z)
  have hi : Function.Injective f := by
    intro x y h
    exact tie.injective (congrArg (fun a : (ℕ ×ₗ ℕ) ×ₗ Fin (Fintype.card (ContactGlued g)) =>
      (ofLex a).2) h)
  let o : LinearOrder (ContactGlued g) := LinearOrder.lift' f hi
  refine ⟨o,?_,?_⟩
  · intro x y h
    change f (contactCoreEmb g x) < f (contactCoreEmb g y)
    exact Prod.Lex.left _ _ (key_core_strict g h)
  · intro i x y h
    change f (contactStandardEmb g hinj i x) < f (contactStandardEmb g hinj i y)
    exact Prod.Lex.left _ _ (key_std_strict g hc hinj i h)

end ContactGluedOrder
end StructuralRamsey.Girth
