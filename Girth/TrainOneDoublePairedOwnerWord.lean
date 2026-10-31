import Girth.TrainActualLongResultLabelWord

/-!
# Paired physical labels and geometric owners in a one-long word

For a selected source position j, the actual long word retains every
other label and inserts exactly two physical-edge labels at j.
We build one literal paired list which attaches to each unchanged
label its old admissible owner, and attaches to BOTH inserted labels
the chosen standard-owner i.

The two projections are exactly the checked one-double words for
labels and owners. Under old admissibility and containment of the
two new physical edges, EVERY paired token is admissible.

This is a genuine word-level owner transport certificate, without
assuming the output n+1 Fin index has yet been identified or proving
minimum cyclic cut nonincrease. Those remain separate obligations.
Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth

universe v w
variable {Label : Type v} {Owner : Type w}

/-- Literal paired owner word for one doubled source occurrence.
Old label-owner pairs remain unchanged; two new labels use one
common target owner. -/
def oneDoublePairedWord {n : ℕ}
    (labels : Fin n → Label) (owners : Fin n → Owner)
    (j : Fin n) (first second : Label) (target : Owner) :
    List (Label × Owner) :=
  (List.ofFn fun k : Fin n =>
    if k = j then [(first, target), (second, target)]
    else [(labels k, owners k)]).flatten

/-- The LABELS of the owner certificate agree with the literal
one-long output label word. -/
theorem oneDoublePairedWord_label_projection
    {n : ℕ} (labels : Fin n → Label) (owners : Fin n → Owner)
    (j : Fin n) (first second : Label) (target : Owner) :
    (oneDoublePairedWord labels owners j first second target).map Prod.fst =
      oneDoubleWord labels j first second := by
  simp only [oneDoublePairedWord, oneDoubleWord,
    List.map_flatten, List.map_ofFn]
  have hBlocks :
      (fun k : Fin n =>
        (if k = j then [(first, target), (second, target)]
         else [(labels k, owners k)]).map Prod.fst) =
      (fun k : Fin n =>
        if k = j then [first, second] else [labels k]) := by
    funext k
    by_cases hk : k = j
    · simp [hk]
    · simp [hk]
  exact congrArg List.flatten (congrArg List.ofFn hBlocks)

/-- The OWNERS of the same certificate are the old owner word with
the selected singleton replaced by two copies of the target owner. -/
theorem oneDoublePairedWord_owner_projection
    {n : ℕ} (labels : Fin n → Label) (owners : Fin n → Owner)
    (j : Fin n) (first second : Label) (target : Owner) :
    (oneDoublePairedWord labels owners j first second target).map Prod.snd =
      oneDoubleWord owners j target target := by
  simp only [oneDoublePairedWord, oneDoubleWord,
    List.map_flatten, List.map_ofFn]
  have hBlocks :
      (fun k : Fin n =>
        (if k = j then [(first, target), (second, target)]
         else [(labels k, owners k)]).map Prod.snd) =
      (fun k : Fin n =>
        if k = j then [target, target] else [owners k]) := by
    funext k
    by_cases hk : k = j
    · simp [hk]
    · simp [hk]
  exact congrArg List.flatten (congrArg List.ofFn hBlocks)

/-- The doubled source label word has length precisely n+1.
This is the exact source/output Fin-size equality required later,
not an informal assumption that one long block inserts one token. -/
theorem oneDoubleWord_length_succ
    {n : ℕ} (labels : Fin n → Label) (j : Fin n)
    (first second : Label) :
    (oneDoubleWord labels j first second).length = n + 1 := by
  obtain ⟨before, after, hOld, hNew⟩ :=
    oneDoubleWord_exists_common_split labels j first second
  have hLen := congrArg List.length hOld
  have hn : before.length + 1 + after.length = n := by
    simp only [List.length_ofFn, List.length_append,
      List.length_cons] at hLen
    omega
  rw [hNew]
  simp only [List.length_append, List.length_cons]
  omega

/-- The paired owner certificate has the same exact output length. -/
theorem oneDoublePairedWord_length_succ
    {n : ℕ} (labels : Fin n → Label) (owners : Fin n → Owner)
    (j : Fin n) (first second : Label) (target : Owner) :
    (oneDoublePairedWord labels owners j first second target).length =
      n + 1 := by
  have h := congrArg List.length
    (oneDoublePairedWord_label_projection
      labels owners j first second target)
  simpa only [List.length_map,
    oneDoubleWord_length_succ] using h

/-- Every token of the paired long certificate is geometrically
admissible when the old positions are admissible and BOTH new
physical labels are contained in the chosen receiving standard.
No common designated source target is postulated. -/
theorem oneDoublePairedWord_admissible
    {n : ℕ} (labels : Fin n → Label) (owners : Fin n → Owner)
    (j : Fin n) (first second : Label) (target : Owner)
    (Allowed : Label → Owner → Prop)
    (hOld : ∀ k : Fin n, Allowed (labels k) (owners k))
    (hFirst : Allowed first target)
    (hSecond : Allowed second target) :
    ∀ z ∈ oneDoublePairedWord labels owners j first second target,
      Allowed z.1 z.2 := by
  have hBlock : ∀ k : Fin n,
      ∀ z ∈ (if k = j then [(first, target), (second, target)]
        else [(labels k, owners k)]),
        Allowed z.1 z.2 := by
    intro k z hz
    by_cases hk : k = j
    · simp only [hk, ite_true, List.mem_cons,
        List.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hFirst
      · exact hSecond
    · simp only [hk, ite_false, List.mem_singleton] at hz
      subst z
      exact hOld k
  intro z hz
  change z ∈ (List.ofFn fun k : Fin n =>
    if k = j then [(first, target), (second, target)]
    else [(labels k, owners k)]).flatten at hz
  obtain ⟨ys, hys, hzy⟩ := List.mem_flatten.mp hz
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp hys
  rw [← hk] at hzy
  exact hBlock k z hzy

end StructuralRamsey.Girth
