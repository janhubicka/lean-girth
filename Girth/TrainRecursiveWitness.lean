import Girth.TrainCutoffWellFounded

/-!
# Conditional assembly of recursive train witnesses

This is the recursion interface of Section 17, not the final train Ramsey
theorem.  The input consists of actual witness-producing operators for the
base vector `[2]`, the cutoff-two step, the larger-cutoff finite partite pass,
and the fixed forest-to-order conversion.  Those operators still have to be
instantiated by the geometric construction.  In particular, no full-system
girth assertion is inferred from a decrease of rank alone.

The witness families may contain all target/colouring parameters.  The
larger-cutoff operator receives witnesses for every positive refinement
depth, so a finite pass can choose different depths for its different active
fibres.  Only those lower-cutoff requests are available to that operator.
The cutoff-two operator receives the converted shorter-train witness.
Conversion is never a recursive call at the original vector.

The assembly produces witness data (in an arbitrary sort), not just an
implication between unspecified existence propositions.  Its domain includes
exactly the nonempty nondecreasing cutoff vectors with entries at least two.
All recursive requests stay in that domain and below the fixed starting
ceiling.  Existing multiplicity-lex theorems supply every rank decrease.

The cross-track inputs are deliberately outside this recursion kernel:
Track A supplies physical minimum-segmentation replacement, old supremeness,
and arbitrary-replacement pullback, including the two-segment/order-one case;
Track B supplies actual generated-wagon strongness and linearity and the
mixed two-standard contained-block obstruction; Track C supplies the actual
all-level adjacent parameters and filling/subcopy system-girth transfer.
The remaining Track D construction inputs include initial tail transfer and
unprocessed-fibre refinability, the genuine `[2]` Ramsey base, the cutoff-two
tail contraction/filling step, the larger-cutoff refinement-forgetting and
girth-increment step, and the segmentation length estimate and forest-to-order
pass.  `Operators` records the resulting construction interfaces; it does
not discharge any of these geometric inputs merely by naming them. The
actual initial-stage and finite-pass components are supplied separately by
`TrainRecursiveWitnessInitialStage` and `TrainRecursiveWitnessConstruction`.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v

/-- The cutoff vectors used by the circulation train induction. -/
structure Admissible (t : List ℕ) : Prop where
  nonempty : t ≠ []
  nondecreasing : t.Pairwise (· ≤ ·)
  two_le : ∀ q ∈ t, 2 ≤ q

/-- A fixed finite ceiling is retained throughout one recursion. -/
def Bounded (M : ℕ) (t : List ℕ) : Prop :=
  ∀ q ∈ t, q ≤ M

theorem admissible_two : Admissible [2] := by
  refine ⟨by simp, by simp, ?_⟩
  intro q hq
  simp only [List.mem_singleton] at hq
  subst q
  exact Nat.le_refl 2

theorem not_admissible_nil : ¬ Admissible [] :=
  fun h => h.nonempty rfl

/-- The cutoff-two request is admissible precisely when its tail is nonempty;
the two lower-bound and monotonicity clauses are inherited. -/
theorem Admissible.tail {q : ℕ} {tail : List ℕ}
    (h : Admissible (q :: tail)) (hne : tail ≠ []) :
    Admissible tail := by
  refine ⟨hne, (List.pairwise_cons.mp h.nondecreasing).2, ?_⟩
  intro a ha
  exact h.two_le a (List.mem_cons_of_mem q ha)

theorem Bounded.tail {M q : ℕ} {tail : List ℕ}
    (h : Bounded M (q :: tail)) : Bounded M tail := by
  intro a ha
  exact h a (List.mem_cons_of_mem q ha)

/-- Arbitrarily many positive-depth copies of `q - 1` preserve the admissible
domain.  No bound on the depth is needed. -/
theorem Admissible.replace {q d : ℕ} {tail : List ℕ}
    (h : Admissible (q :: tail)) (hq : 2 < q) (hd : 0 < d) :
    Admissible (List.replicate d (q - 1) ++ tail) := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_replicate, List.length_nil] at hlen
    omega
  · rw [List.pairwise_append]
    refine ⟨List.pairwise_replicate.mpr (Or.inr (Nat.le_refl _)),
      (List.pairwise_cons.mp h.nondecreasing).2, ?_⟩
    intro a ha b hb
    have haeq : a = q - 1 := List.eq_of_mem_replicate ha
    have hqb := (List.pairwise_cons.mp h.nondecreasing).1 b hb
    omega
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · have haeq : a = q - 1 := List.eq_of_mem_replicate ha
      omega
    · exact h.two_le a (List.mem_cons_of_mem q ha)

theorem Bounded.replace {M q d : ℕ} {tail : List ℕ}
    (h : Bounded M (q :: tail)) :
    Bounded M (List.replicate d (q - 1) ++ tail) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · have haeq : a = q - 1 := List.eq_of_mem_replicate ha
    have hq : q ≤ M := h q (by simp)
    omega
  · exact h a (List.mem_cons_of_mem q ha)

/-- Explicit obligations at the boundary with the geometric partite proof.

`ForestWitness t` and `OrderWitness t` must retain all intended invariants,
including mixed bottom forests, parameters, and every tail cycle condition.
This record does not construct those families or prove those invariants.
The fields are operators on actual witness data, not axioms or admitted
instances.  The final application must supply each field independently.

`largerCutoff` is the whole finite partite pass at the current cutoff.  It
receives the already constructed universal witnesses at all smaller
positive refinement depths.  It does not receive the current witness.
-/
structure Operators
    (ForestWitness : List ℕ → Sort u)
    (OrderWitness : List ℕ → Sort v) where
  baseTwo : ForestWitness [2]
  forestToOrder : ∀ t, Admissible t → ForestWitness t → OrderWitness t
  cutoffTwo : ∀ tail, Admissible tail →
    OrderWitness tail → ForestWitness (2 :: tail)
  largerCutoff : ∀ q tail, Admissible (q :: tail) → 2 < q →
    (∀ d, 0 < d → ForestWitness (List.replicate d (q - 1) ++ tail)) →
    ForestWitness (q :: tail)

/-- Assemble data-valued witnesses using the three genuine recursion cases.
The only recursive calls are those listed in the manuscript. -/
noncomputable def Operators.assembleBounded
    {ForestWitness : List ℕ → Sort u}
    {OrderWitness : List ℕ → Sort v}
    (ops : Operators ForestWitness OrderWitness) (M : ℕ) :
    ∀ t, Admissible t → Bounded M t → ForestWitness t := by
  refine (trainCountLex_wellFounded M).fix
    (C := fun t => Admissible t → Bounded M t → ForestWitness t) ?_
  intro t ih hValid hBound
  cases t with
  | nil => exact False.elim (hValid.nonempty rfl)
  | cons q tail =>
      have hq : 2 ≤ q := hValid.two_le q (by simp)
      have hqM : q ≤ M := hBound q (by simp)
      by_cases htwo : q = 2
      · subst q
        cases tail with
        | nil => exact ops.baseTwo
        | cons a tail =>
            have ht : Admissible (a :: tail) := hValid.tail (by simp)
            have hb : Bounded M (a :: tail) := hBound.tail
            exact ops.cutoffTwo (a :: tail) ht
              (ops.forestToOrder (a :: tail) ht
                (ih (a :: tail)
                  (trainCutoffDropTwo_wfRankDecrease M (a :: tail) hqM)
                  ht hb))
      · have hlarge : 2 < q := by omega
        apply ops.largerCutoff q tail hValid hlarge
        intro d hd
        exact ih (List.replicate d (q - 1) ++ tail)
          (trainCutoffReplacement_wfRankDecrease M q d tail hlarge hqM)
          (hValid.replace hlarge hd) hBound.replace

/-- A canonical ceiling removes a separately chosen global bound from the
public assembly interface. -/
def ceiling (t : List ℕ) : ℕ := t.foldr max 2

theorem bounded_ceiling (t : List ℕ) : Bounded (ceiling t) t := by
  induction t with
  | nil => simp [Bounded]
  | cons a t ih =>
      intro q hq
      rcases List.mem_cons.mp hq with hq | hq
      · subst q
        exact le_max_left _ _
      · exact (ih q hq).trans (le_max_right _ _)

/-- Conditional recursive witness existence without a separately supplied
starting ceiling.  Concrete train geometry is exactly the `Operators` input.
-/
noncomputable def Operators.assemble
    {ForestWitness : List ℕ → Sort u}
    {OrderWitness : List ℕ → Sort v}
    (ops : Operators ForestWitness OrderWitness)
    (t : List ℕ) (ht : Admissible t) : ForestWitness t :=
  ops.assembleBounded (ceiling t) t ht (bounded_ceiling t)

/-- Obtain the order witness only after constructing the forest witness at
the same vector.  This final conversion does not enlarge the recursion.
-/
noncomputable def Operators.assembleOrder
    {ForestWitness : List ℕ → Sort u}
    {OrderWitness : List ℕ → Sort v}
    (ops : Operators ForestWitness OrderWitness)
    (t : List ℕ) (ht : Admissible t) : OrderWitness t :=
  ops.forestToOrder t ht (ops.assemble t ht)

end StructuralRamsey.Girth.TrainRecursiveWitness
