import Girth.ContactShorterTrain
import Girth.ContactCopyRestriction

/-! The chosen copy of the original train inside one padded and
filled component. Its edges retain their original labels through
the actual first wagon and the template-edge embedding. This is
the local scattering geometry required in the cutoff-two proof. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X F J : Type v}

namespace ContactWagonPadding
variable {m : ℕ} {D : ContactHypergraphData V E I}
    {T : ContactTrainData E (m+1)}
    (A : ContactWagonPadding
      (D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier X)
    (L : ContactHypergraphData X F J)

abbrev first (_A : ContactWagonPadding
      (D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier X) (e : E) : T.FirstWagon := T.parent (0 : Fin (m+1)).succ e

def firstMember (e : E) (x : V) (hx : x ∈ D.edgeCarrier e) :
    (D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier (A.first e) :=
  ⟨x,e,rfl,hx⟩

/-- An actual strongly induced embedding of each original first
wagon into X, including its edge labels. The vertex embeddings are
the maps already used to pad the wagons. -/
structure TemplateEmbedding where
  edge : E → F
  edge_image : ∀ e, L.edgeCarrier (edge e) =
    {x | ∃ y (hy : y ∈ D.edgeCarrier e), A.inside (A.first e) (A.firstMember e y hy) = x}
  edge_inj : ∀ e f, A.first e = A.first f → edge e = edge f → e = f
  strong : ∀ p : T.FirstWagon, ∀ f,
    (L.edgeCarrier f ∩ Set.range (A.inside p)).Nontrivial →
      ∃ e, A.first e = p ∧ edge e = f

namespace TemplateEmbedding
variable (M : A.TemplateEmbedding L)

def chosenEdge : E ↪ (T.FirstWagon × F) where
  toFun e := (A.first e,M.edge e)
  inj' := fun e f h => M.edge_inj e f (congrArg Prod.fst h) (congrArg Prod.snd h)

variable (hcover : ∀ x, ∃ f, x ∈ L.edgeCarrier f) (hne : Nonempty F)

noncomputable def Filled (_M : A.TemplateEmbedding L) := (A.filling L hcover hne).output

theorem chosen_carrier (e : E) :
    (M.Filled hcover hne).edgeCarrier (M.chosenEdge e) =
      A.oldVertex '' D.edgeCarrier e := by
  change A.place (A.first e) '' L.edgeCarrier (M.edge e) = _
  rw [M.edge_image e]
  ext z
  constructor
  · rintro ⟨x,⟨y,hy,rfl⟩,he⟩
    have he' := A.placeFun_old (A.first e) (A.firstMember e y hy)
    exact ⟨y,hy,he'.symm.trans he⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨A.inside (A.first e) (A.firstMember e y hy),⟨y,hy,rfl⟩,
      A.placeFun_old (A.first e) (A.firstMember e y hy)⟩

/-- Positive relations of the filled shorter train restrict to
the original train. At bottom this is the injective edge map. -/
theorem chosen_rel (μ : Fin (m+2)) (e f : E) :
    ((A.filling L hcover hne).fillTrain T.shorterTrain).parent μ (M.chosenEdge e) =
      ((A.filling L hcover hne).fillTrain T.shorterTrain).parent μ (M.chosenEdge f) ↔
      T.parent μ e = T.parent μ f := by
  refine Fin.cases ?_ (fun ν => ?_) μ
  · change M.chosenEdge e = M.chosenEdge f ↔ _
    exact ⟨fun he => congrArg (T.parent 0) (M.chosenEdge.injective he),
      fun he => congrArg M.chosenEdge (T.bottom he)⟩
  · change T.shorterParent ν (A.first e) = T.shorterParent ν (A.first f) ↔ _
    rw [T.shorterParent_first,T.shorterParent_first]

/-- If a filled edge meets the original vertex set in two
points, its template edge meets the embedded first wagon in
two points. Strong inducedness of that embedding supplies an
actual original edge with exactly this label. -/
theorem chosen_strong (p : T.FirstWagon × F)
    (h : ((M.Filled hcover hne).edgeCarrier p ∩ Set.range A.oldVertex).Nontrivial) :
    p ∈ Set.range M.chosenEdge := by
  rcases p with ⟨p,f⟩
  obtain ⟨u,hu,w,hw,huv⟩ := h
  obtain ⟨x,hx,he⟩ := hu.1
  obtain ⟨y,hy,hf⟩ := hw.1
  have hxy : x ≠ y := fun heq => huv (he.symm.trans
    ((congrArg (A.place p) heq).trans hf))
  have hinside (z : X) (hmem : A.place p z ∈ Set.range A.oldVertex) :
      z ∈ Set.range (A.inside p) := by
    by_contra hn
    obtain ⟨v,hv⟩ := hmem
    change A.oldVertex v = A.placeFun p z at hv
    rw [A.placeFun_private p z hn] at hv
    cases hv
  have hux : A.place p x ∈ Set.range A.oldVertex := he.symm ▸ hu.2
  have hwy : A.place p y ∈ Set.range A.oldVertex := hf.symm ▸ hw.2
  obtain ⟨e,he',hf'⟩ := M.strong p f
    ⟨x,⟨hx,hinside x hux⟩,y,⟨hy,hinside y hwy⟩,hxy⟩
  exact ⟨e,Prod.ext he' hf'⟩

/-- At any inherited cut, every original vertex on a filled
wagon has a chosen original edge in that wagon through it.
This is condition (i) of copy restriction. -/
theorem chosen_incidence (ν : Fin (m+1)) (x : V)
    (p : T.Wagon ν.succ)
    (hx : A.oldVertex x ∈
      ((M.Filled hcover hne).atCut
        (((A.filling L hcover hne).fillTrain T.shorterTrain).parent ν.succ)).contactWagonCarrier p) :
    ∃ e : E, T.parent ν.succ e = p ∧ x ∈ D.edgeCarrier e := by
  obtain ⟨⟨r,f⟩,hr,hxf⟩ := hx
  have hpad := (A.filling L hcover hne).output_contained (r,f) hxf
  change A.oldVertex x ∈ A.padded r at hpad
  obtain ⟨e,he,hxe⟩ := (A.old_mem_padded r x).mp hpad
  refine ⟨e,?_,hxe⟩
  change T.shorterParent ν r = p at hr
  exact (T.shorterParent_first ν e).symm.trans
    ((congrArg (T.shorterParent ν) he).trans hr)

/-- Any common vertex of distinct inherited wagons belongs to the
original vertex set. This is condition (ii) of copy restriction. -/
theorem wagon_intersection_chosen (ν : Fin (m+1))
    (p r : T.Wagon ν.succ) (hne' : p ≠ r) :
    (((M.Filled hcover hne).atCut
        (((A.filling L hcover hne).fillTrain T.shorterTrain).parent ν.succ)).contactWagonCarrier p ∩
      ((M.Filled hcover hne).atCut
        (((A.filling L hcover hne).fillTrain T.shorterTrain).parent ν.succ)).contactWagonCarrier r) ⊆
      Set.range A.oldVertex := by
  intro x hx
  obtain ⟨⟨a,f⟩,ha,hxf⟩ := hx.1
  obtain ⟨⟨b,g⟩,hb,hxg⟩ := hx.2
  have hne'' : a ≠ b := by
    intro he
    change T.shorterParent ν a = p at ha
    change T.shorterParent ν b = r at hb
    exact hne' (ha.symm.trans ((congrArg (T.shorterParent ν) he).trans hb))
  have hpad : x ∈ A.padded a ∩ A.padded b :=
    ⟨(A.filling L hcover hne).output_contained (a,f) hxf,
      (A.filling L hcover hne).output_contained (b,g) hxg⟩
  rw [A.padded_intersection a b hne''] at hpad
  obtain ⟨y,_,he⟩ := hpad
  exact ⟨y,he⟩

end TemplateEmbedding
end ContactWagonPadding

/-- Vector-colour extraction in cutoff two. For every colouring of
the filled edges (old edge, template edge), apply the shorter-train
arrow to the vector colour. A common vector colour on its selected
copy and a monochromatic template line give a monochromatic
chosen original train. The actual selected edge map is returned. -/
theorem contact_cutoffTwo_arrow {P S K C : Type v}
    (first : E → P) (template : S → E → F)
    (embed : K → (S × P) → I)
    (hshort : ∀ χ : I → (F → C), ∃ j : K, ∃ ρ : F → C,
      ∀ s p, χ (embed j (s,p)) = ρ)
    (hline : ∀ ρ : F → C, ∃ s : S, ∃ c : C, ∀ e, ρ (template s e) = c)
    (χ : I × F → C) :
    ∃ j : K, ∃ s : S, ∃ c : C,
      ∀ e, χ (embed j (s,first e),template s e) = c := by
  obtain ⟨j,ρ,hj⟩ := hshort (fun i f => χ (i,f))
  obtain ⟨s,c,hs⟩ := hline ρ
  exact ⟨j,s,c,fun e => (congrFun (hj s (first e)) (template s e)).trans (hs e)⟩

end StructuralRamsey.Girth
