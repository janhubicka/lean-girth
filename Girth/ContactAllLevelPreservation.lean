import Girth.ContactTrainBottom
import Girth.ContactPositivePreservation
import Girth.ContactBottomPreservation
import Girth.ContactMixedForestConverse
import Girth.ContactTrainParameters

/-! One common output train carries all the required proper-level
system-girth bounds. The positive-cut preservation theorem and the
mixed-forest bottom alternative are applied to the actual cuts of
that train, not to unrelated witnesses. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ : Type v}

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)

/-- Proper levels only; the value of the bound function at the
universal top is deliberately immaterial. -/
def SystemBounds {m : ℕ} (T : ContactTrainData E m)
    (q : Fin (m+1) → ℕ) : Prop :=
  ∀ μ, μ.val < m → (D.atCut (T.parent μ)).ContactSystemGirthGT (q μ)

def PositiveBounds {m : ℕ} (T : ContactTrainData E m)
    (q : Fin (m+1) → ℕ) : Prop :=
  ∀ μ, 0 < μ.val → μ.val < m →
    (D.atCut (T.parent μ)).ContactSystemGirthGT (q μ)

/-- The parameters at adjacent levels, expressed with the
allowed sets of real vertices. -/
def Parameters {m : ℕ} (T : ContactTrainData E m)
    (allowed : Fin m → Set V) : Prop :=
  ∀ j : Fin m, D.Parameter T j.castSucc j.succ (allowed j)

end ContactHypergraphData

namespace ContactTrainStrip
variable {m : ℕ}
    {D : ContactHypergraphData V E I} {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E m} {S : ContactTrainData E₀ m}
    (A : ContactTrainStrip D L T S)

theorem preserves_positiveBounds (q : Fin (m+1) → ℕ)
    (hq : ∀ μ, 0 < μ.val → μ.val < m → 2 ≤ q μ)
    (hs : A.StripStrong)
    (hD : D.PositiveBounds T q) (hL : L.PositiveBounds S q) :
    A.outputHypergraph.PositiveBounds A.outputTrain q := by
  intro μ hpos hproper
  have h := (A.atCut μ).preserves_systemGirth_positive (hq μ hpos hproper)
    (A.stripStrong_atCut hs μ) (hD μ hpos hproper) (hL μ hpos hproper)
  rw [A.cut_output_eq μ] at h
  exact h

/-- The literal edge-label bottom picture supplies the bottom
bound on the same generated output train. -/
theorem preserves_bottomBound {q : ℕ} (hs : A.StripStrong)
    (ha : A.StripAbsorption)
    (hD : D.bottomCut.ZeroMixedForestsThrough q)
    (hsub : ∀ i e, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial)
    (hL : (L.atCut (S.parent ⟨0,by omega⟩)).ContactSystemGirthGT q) :
    (A.outputHypergraph.atCut (A.outputTrain.parent ⟨0,by omega⟩)).ContactSystemGirthGT q := by
  let P := A.bottomPicture
  have hL' := (S.bottom_systemGirth_iff L q).mp hL
  have hc := P.core_strong (A.stripStrong_bottom hs)
  have hpar : Function.Injective P.output.parent := by
    intro e f he
    rw [A.bottomPicture_parent,A.bottomPicture_parent] at he
    exact he
  have hout := P.pictureCopies.preserves_systemGirth_bottom
    (fun _ => rfl) hpar (A.bottomAbsorption_of_strip ha) hc
    hD.1 hsub hsize hD.2 hL'
  change A.bottomPicture.output.ContactSystemGirthGT q at hout
  rw [A.bottomPicture_output_eq] at hout
  exact (A.outputTrain.bottom_systemGirth_iff A.outputHypergraph q).mpr hout

/-- Full one-step preservation at every proper level, with the
mixed-forest rather than system-girth hypothesis at the bottom
core. This is precisely the combination used in the induction. -/
theorem preserves_systemBounds (q : Fin (m+1) → ℕ)
    (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (hs : A.StripStrong) (ha : A.StripAbsorption)
    (hD0 : D.bottomCut.ZeroMixedForestsThrough (q ⟨0,by omega⟩))
    (hD : D.PositiveBounds T q) (hL : L.SystemBounds S q)
    (hsub : ∀ i e, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial) :
    A.outputHypergraph.SystemBounds A.outputTrain q := by
  have hpos := A.preserves_positiveBounds q (fun μ _ h => hq μ h)
    hs hD (fun μ _ h => hL μ h)
  intro μ hproper
  by_cases hz : μ.val = 0
  · have he : μ = (⟨0,by omega⟩ : Fin (m+1)) := Fin.ext hz
    subst μ
    exact A.preserves_bottomBound hs ha hD0 hsub hsize (hL _ hproper)
  · exact hpos μ (by omega) hproper

/-- After the bottom preservation step the mixed forests of the
output follow from its bottom system girth. -/
theorem output_mixedForests_of_bounds [Fintype A.Vertex] {q : Fin (m+1) → ℕ}
    (hm : 0 < m)
    (h : A.outputHypergraph.SystemBounds A.outputTrain q) :
    A.outputHypergraph.bottomCut.ZeroMixedForestsThrough (q ⟨0,by omega⟩) := by
  have hb := h ⟨0,by omega⟩ hm
  exact A.outputHypergraph.bottomCut.zero_mixedForests_of_systemGirth (fun _ => rfl)
    ((A.outputTrain.bottom_systemGirth_iff A.outputHypergraph _).mp hb)

/-- Parameters on the common output train, with positive proper
G1/G2 and only no isolated vertices at the top. -/
theorem preserves_parameters (allowed : Fin m → Set A.Vertex)
    (hD : D.Parameters T (fun j => A.coreV ⁻¹' allowed j))
    (hL : ∀ i, L.Parameters S (fun j => A.stdV i ⁻¹' allowed j))
    (hgeom : ∀ μ : Fin (m+1), 0 < μ.val → μ.val < m →
      (D.atCut (T.parent μ)).ContactG1 ∧ (D.atCut (T.parent μ)).ContactG2)
    (hcover : ∀ i x, x ∈ D.copyCarrier i →
      ∃ e, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e) :
    A.outputHypergraph.Parameters A.outputTrain allowed := by
  intro j
  have hpos : 0 < j.succ.val := by simp
  by_cases hproper : j.succ.val < m
  · have hg := hgeom j.succ hpos hproper
    exact A.preserves_parameter_proper j.castSucc j.succ (allowed j)
      (hD j) (fun i => hL i j) hg.1 hg.2
  · have he : j.succ = (⟨m,by omega⟩ : Fin (m+1)) := by
      apply Fin.ext
      have hj := j.succ.isLt
      omega
    have hc := hD j
    have hl : ∀ i, L.Parameter S j.castSucc j.succ (A.stdV i ⁻¹' allowed j) :=
      fun i => hL i j
    change A.outputHypergraph.Parameter A.outputTrain j.castSucc j.succ (allowed j)
    rw [he] at hc hl ⊢
    exact A.preserves_parameter_top j.castSucc (allowed j) hc hl hcover

end ContactTrainStrip
end StructuralRamsey.Girth
