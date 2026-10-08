import Girth.BoundaryGirthExtension
import Girth.ForestObservableEventBound
import Mathlib.Tactic

/-!
# Short-path boundary records for successor histories

For a single fresh edge, preservation of Berge girth is determined by the
short-path relation between the marked attachment points, provided all old
contacts of the fresh edge occur at those points. This is distinct from the
pair-shadow, which detects linearity but not arbitrary girth.

The record is finite and monotone for an increasing family of old edge sets.
No claim is made that it controls B-carrier ownership, running intersections,
or every intrinsic successor event.
-/

namespace StructuralRamsey.Girth

universe u v w

/-- Short Berge paths between two named boundary vertices. -/
def MarkedShortBergePath {I : Type u} {W : Type v}
    (H : Set (Set W)) (f : I → W) (g : ℕ) (i j : I) : Prop :=
  ∃ p : BergePath H, p.length < g ∧
    p.vertex 0 = f i ∧ p.vertex (Fin.last p.length) = f j

private theorem bergePath_endpoints_incident
    {W : Type v} {H : Set (Set W)} (p : BergePath H) :
    (∃ a ∈ H, p.vertex 0 ∈ a) ∧
      (∃ a ∈ H, p.vertex (Fin.last p.length) ∈ a) := by
  let first : Fin p.length := ⟨0, by have h := p.hlength; omega⟩
  let last : Fin p.length := ⟨p.length - 1, by have h := p.hlength; omega⟩
  constructor
  · refine ⟨p.edge first, p.edge_mem first, ?_⟩
    simpa [first] using p.left_mem first
  · refine ⟨p.edge last, p.edge_mem last, ?_⟩
    have hlast : last.succ = Fin.last p.length := by
      apply Fin.ext
      change p.length - 1 + 1 = p.length
      have h := p.hlength
      omega
    simpa only [hlast] using p.right_mem last

/-- Exact contact with marked boundary vertices, restricted to points lying
on at least one old hyperedge. Fresh vertices have no old incidence. -/
private theorem freshContact_mem_iff
    {I : Type u} {W : Type v}
    (H : Set (Set W)) (f : I → W) (S : Set I) (e : Set W)
    (hContact : ∀ a ∈ H, e ∩ a = (f '' S) ∩ a)
    (x : W) (hIncident : ∃ a ∈ H, x ∈ a) :
    x ∈ e ↔ x ∈ f '' S := by
  obtain ⟨a, ha, hxa⟩ := hIncident
  constructor
  · intro he
    have hxa' : x ∈ e ∩ a := ⟨he, hxa⟩
    rw [hContact a ha] at hxa'
    exact hxa'.1
  · intro hf
    have hxa' : x ∈ (f '' S) ∩ a := ⟨hf, hxa⟩
    rw [← hContact a ha] at hxa'
    exact hxa'.1

/-- The contact assumption lets us replace the proposed edge by the fixed
set of marked boundary positions in the short-path obstruction. -/
theorem hasShortBergePathToEdge_iff_marked
    {I : Type u} {W : Type v}
    (H : Set (Set W)) (f : I → W) (S : Set I) (e : Set W) (g : ℕ)
    (hContact : ∀ a ∈ H, e ∩ a = (f '' S) ∩ a) :
    HasShortBergePathToEdge H e g ↔
      ∃ i ∈ S, ∃ j ∈ S, MarkedShortBergePath H f g i j := by
  constructor
  · rintro ⟨p, hlen, hstart, hend⟩
    obtain ⟨hincidentStart, hincidentEnd⟩ := bergePath_endpoints_incident p
    have hmarkStart : p.vertex 0 ∈ f '' S :=
      (freshContact_mem_iff H f S e hContact _ hincidentStart).mp hstart
    have hmarkEnd : p.vertex (Fin.last p.length) ∈ f '' S :=
      (freshContact_mem_iff H f S e hContact _ hincidentEnd).mp hend
    obtain ⟨i, hi, hiEq⟩ := hmarkStart
    obtain ⟨j, hj, hjEq⟩ := hmarkEnd
    exact ⟨i, hi, j, hj, p, hlen, hiEq.symm, hjEq.symm⟩
  · rintro ⟨i, hi, j, hj, p, hlen, hfirst, hlast⟩
    obtain ⟨hincidentStart, hincidentEnd⟩ := bergePath_endpoints_incident p
    have hmarkStart : p.vertex 0 ∈ f '' S := ⟨i, hi, hfirst.symm⟩
    have hmarkEnd : p.vertex (Fin.last p.length) ∈ f '' S :=
      ⟨j, hj, hlast.symm⟩
    exact ⟨p, hlen,
      (freshContact_mem_iff H f S e hContact _ hincidentStart).mpr hmarkStart,
      (freshContact_mem_iff H f S e hContact _ hincidentEnd).mpr hmarkEnd⟩

/-- A short old path remains a short path when old edges are retained. -/
theorem markedShortBergePath_mono
    {I : Type u} {W : Type v}
    (H K : Set (Set W)) (hHK : H ⊆ K) (f : I → W) (g : ℕ) (i j : I)
    (h : MarkedShortBergePath H f g i j) :
    MarkedShortBergePath K f g i j := by
  obtain ⟨p, hlen, hfirst, hlast⟩ := h
  exact ⟨p.ofEdgeMem (fun t => hHK (p.edge_mem t)), hlen, hfirst, hlast⟩

/-- Marked short-path agreement is sufficient for equivalent girth outcomes
of two fresh-edge attachments, assuming each old host already has girth >g. -/
theorem freshEdge_girth_iff_of_sameShortPaths
    {I : Type u} {W : Type v} {Z : Type w}
    (H : Set (Set W)) (K : Set (Set Z))
    (f : I → W) (f' : I → Z) (S : Set I)
    (e : Set W) (e' : Set Z) (g : ℕ)
    (hOld : GirthGT H g) (hOld' : GirthGT K g)
    (hNew : e ∉ H) (hNew' : e' ∉ K)
    (hContact : ∀ a ∈ H, e ∩ a = (f '' S) ∩ a)
    (hContact' : ∀ a ∈ K, e' ∩ a = (f' '' S) ∩ a)
    (hPaths : ∀ i j, MarkedShortBergePath H f g i j ↔
      MarkedShortBergePath K f' g i j) :
    GirthGT (insert e H) g ↔ GirthGT (insert e' K) g := by
  rw [girthGT_insert_iff_no_shortBergePath H e g hNew,
    girthGT_insert_iff_no_shortBergePath K e' g hNew']
  simp only [hOld, hOld', true_and]
  rw [hasShortBergePathToEdge_iff_marked H f S e g hContact,
    hasShortBergePathToEdge_iff_marked K f' S e' g hContact']
  constructor
  · intro h ⟨i, hi, j, hj, hp⟩
    exact h ⟨i, hi, j, hj, (hPaths i j).mpr hp⟩
  · intro h ⟨i, hi, j, hj, hp⟩
    exact h ⟨i, hi, j, hj, (hPaths i j).mp hp⟩

/-- The finite ordered-pair record at a fixed girth cutoff. -/
noncomputable def markedShortPathRecord
    {I : Type u} {W : Type v} [Fintype I]
    (H : Set (Set W)) (f : I → W) (g : ℕ) : Finset (I × I) := by
  classical
  exact Finset.univ.filter (fun ij =>
    MarkedShortBergePath H f g ij.1 ij.2)

@[simp] theorem mem_markedShortPathRecord
    {I : Type u} {W : Type v} [Fintype I]
    (H : Set (Set W)) (f : I → W) (g : ℕ) (ij : I × I) :
    ij ∈ markedShortPathRecord H f g ↔
      MarkedShortBergePath H f g ij.1 ij.2 := by
  classical
  simp [markedShortPathRecord]

theorem markedShortPathRecord_mono
    {I : Type u} {W : Type v} [Fintype I]
    (H K : Set (Set W)) (hHK : H ⊆ K) (f : I → W) (g : ℕ) :
    markedShortPathRecord H f g ⊆ markedShortPathRecord K f g := by
  intro ij hij
  rw [mem_markedShortPathRecord] at hij ⊢
  exact markedShortBergePath_mono H K hHK f g ij.1 ij.2 hij

/-- Along a nested support process on fixed marked vertices, steps which
strictly change this cutoff record are bounded by the number of ordered
marked-vertex pairs. Neutral stages are not counted. -/
theorem markedShortPathChanges_bound
    {I : Type u} {W : Type v} [Fintype I]
    (H : ℕ → Set (Set W)) (f : I → W) (g N : ℕ)
    (active : ℕ → Prop) [DecidablePred active]
    (hMono : ∀ n, n < N → H n ⊆ H (n + 1))
    (hActive : ∀ n, n < N → active n →
      markedShortPathRecord (H n) f g ⊂
        markedShortPathRecord (H (n + 1)) f g) :
    ((Finset.range N).filter active).card ≤
      Fintype.card I * Fintype.card I := by
  have h := activeRecordSteps_le
    (fun n => markedShortPathRecord (H n) f g) active N
    (fun n hn => markedShortPathRecord_mono _ _ (hMono n hn) f g) hActive
  simpa using h

/-- The finite boundary certificate, rather than a pointwise family of
propositions, can be used directly to replay a one-edge girth test.  The
contact and old-girth assumptions remain indispensable. -/
theorem freshEdge_girth_iff_of_equalShortPathRecords
    {I : Type u} [Fintype I] {W : Type v} {Z : Type w}
    (H : Set (Set W)) (K : Set (Set Z))
    (f : I → W) (f' : I → Z) (S : Set I)
    (e : Set W) (e' : Set Z) (g : ℕ)
    (hOld : GirthGT H g) (hOld' : GirthGT K g)
    (hNew : e ∉ H) (hNew' : e' ∉ K)
    (hContact : ∀ a ∈ H, e ∩ a = (f '' S) ∩ a)
    (hContact' : ∀ a ∈ K, e' ∩ a = (f' '' S) ∩ a)
    (hRecord : markedShortPathRecord H f g =
      markedShortPathRecord K f' g) :
    GirthGT (insert e H) g ↔ GirthGT (insert e' K) g := by
  apply freshEdge_girth_iff_of_sameShortPaths
    H K f f' S e e' g hOld hOld' hNew hNew' hContact hContact'
  intro i j
  have hPair :
      ((i, j) : I × I) ∈ markedShortPathRecord H f g ↔
        ((i, j) : I × I) ∈ markedShortPathRecord K f' g := by
    rw [hRecord]
  simpa only [mem_markedShortPathRecord] using hPair

end StructuralRamsey.Girth
