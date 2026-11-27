import Girth.ContactRefinementGirth

/-! Forgetting inserted levels in a refinement. The retained
wagon labels and the underlying hypergraph are literally unchanged.
The only parameter calculation is descent across the omitted cuts. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I : Type v}

namespace ContactTrainData
variable {m n : ℕ} (T : ContactTrainData E m)

def retainLevels (f : Fin (n+1) → Fin (m+1))
    (hf : Monotone f)
    (h0 : f ⟨0,by omega⟩ = ⟨0,by omega⟩)
    (ht : f ⟨n,by omega⟩ = ⟨m,by omega⟩) :
    ContactTrainData E n where
  Wagon := fun i => T.Wagon (f i)
  parent := fun i => T.parent (f i)
  surj := fun i => T.surj (f i)
  nested := fun i j h e e' he => T.nested (f i) (f j) (hf h) e e' he
  bottom := by
    rw [h0]
    exact T.bottom
  top := by
    rw [ht]
    exact T.top

end ContactTrainData

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)
variable {m n : ℕ} (T : ContactTrainData E m)

theorem parameter_trans (μ ν ρ : Fin (m+1)) (allowed : Set V)
    (h1 : D.Parameter T μ ν allowed) (h2 : D.Parameter T ν ρ allowed) :
    D.Parameter T μ ρ allowed := by
  intro e f x hp hx hy hn
  exact h1 e f x (h2 e f x hp hx hy hn) hx hy hn

theorem parameter_mono (μ ν : Fin (m+1)) {A B : Set V}
    (h : A ⊆ B) (hp : D.Parameter T μ ν A) :
    D.Parameter T μ ν B :=
  fun e f x he hx hy hn => hp e f x he hx hy (fun ha => hn (h ha))

/-- Descent across consecutive levels, with a common larger
allowed set. This proves that merging several singleton-part
parameters back into the first old parameter is legitimate. -/
theorem parameter_interval (μ ν : Fin (m+1)) (hle : μ ≤ ν)
    (allowed : Fin m → Set V) (B : Set V)
    (hp : D.Parameters T allowed)
    (hsub : ∀ j : Fin m, μ.val ≤ j.val → j.val < ν.val → allowed j ⊆ B) :
    D.Parameter T μ ν B := by
  have aux : ∀ k : ℕ, ∀ hk : μ.val+k ≤ ν.val,
      D.Parameter T μ ⟨μ.val+k,by have := ν.isLt; omega⟩ B := by
    intro k
    induction k with
    | zero =>
      intro hk
      have he : (⟨μ.val+0,by have := ν.isLt; omega⟩ : Fin (m+1)) = μ :=
        Fin.ext (by simp)
      rw [he]
      exact fun _ _ _ h _ _ _ => h
    | succ k ih =>
      intro hk
      let j : Fin m := ⟨μ.val+k,by have := ν.isLt; omega⟩
      have hj : j.val < ν.val := by change μ.val+k < ν.val; omega
      have hparam := D.parameter_mono T j.castSucc j.succ
        (hsub j (by change μ.val ≤ μ.val+k; omega) hj) (hp j)
      have hprev : D.Parameter T μ j.castSucc B := ih (by omega)
      exact D.parameter_trans T μ j.castSucc j.succ B hprev hparam
  have he : (⟨μ.val+(ν.val-μ.val),by have := ν.isLt; omega⟩ : Fin (m+1)) = ν := by
    apply Fin.ext
    change μ.val+(ν.val-μ.val) = ν.val
    have h : μ.val ≤ ν.val := hle
    omega
  have hh := aux (ν.val-μ.val) (by have h : μ.val ≤ ν.val := hle; omega)
  rw [he] at hh
  exact hh

theorem retain_systemBounds (f : Fin (n+1) → Fin (m+1))
    (hf : StrictMono f)
    (h0 : f ⟨0,by omega⟩ = ⟨0,by omega⟩)
    (ht : f ⟨n,by omega⟩ = ⟨m,by omega⟩)
    (q : Fin (m+1) → ℕ) (h : D.SystemBounds T q) :
    D.SystemBounds (T.retainLevels f hf.monotone h0 ht) (q ∘ f) := by
  intro i hi
  have hlt : f i < f (⟨n,by omega⟩ : Fin (n+1)) := hf (by exact hi)
  rw [ht] at hlt
  exact h (f i) hlt

theorem retain_positiveBounds (f : Fin (n+1) → Fin (m+1))
    (hf : StrictMono f)
    (h0 : f ⟨0,by omega⟩ = ⟨0,by omega⟩)
    (ht : f ⟨n,by omega⟩ = ⟨m,by omega⟩)
    (q : Fin (m+1) → ℕ) (h : D.PositiveBounds T q) :
    D.PositiveBounds (T.retainLevels f hf.monotone h0 ht) (q ∘ f) := by
  intro i hi hj
  have hlo : f (⟨0,by omega⟩ : Fin (n+1)) < f i := hf (by exact hi)
  have hhi : f i < f (⟨n,by omega⟩ : Fin (n+1)) := hf (by exact hj)
  rw [h0] at hlo
  rw [ht] at hhi
  exact h (f i) hlo hhi

theorem retain_parameters (f : Fin (n+1) → Fin (m+1))
    (hf : StrictMono f)
    (h0 : f ⟨0,by omega⟩ = ⟨0,by omega⟩)
    (ht : f ⟨n,by omega⟩ = ⟨m,by omega⟩)
    (allowed : Fin m → Set V) (oldAllowed : Fin n → Set V)
    (h : D.Parameters T allowed)
    (hsub : ∀ j : Fin n, ∀ k : Fin m,
      (f j.castSucc).val ≤ k.val → k.val < (f j.succ).val →
        allowed k ⊆ oldAllowed j) :
    D.Parameters (T.retainLevels f hf.monotone h0 ht) oldAllowed := by
  intro j
  have hle : f j.castSucc ≤ f j.succ := hf.monotone (by
    change j.val ≤ j.val+1
    omega)
  exact D.parameter_interval T (f j.castSucc) (f j.succ) hle allowed
    (oldAllowed j) h (hsub j)

end ContactHypergraphData
end StructuralRamsey.Girth
