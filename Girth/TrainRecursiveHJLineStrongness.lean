import Girth.TrainRecursiveHJTwoPointRigidity

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual Hales--Jewett lines have A-strong image under A-linearity

The induced partite Hales--Jewett power is a larger A-partite Ramsey
BASE, not in general a high-girth structure. Its literal line embeddings
nevertheless have A-strong range when the original target is A-linear
and every ambient A-copy of the power preserves the A-part map.

The reason is coordinatewise. Two distinct points of an ambient
A-copy lying on the same HJ line determine its coordinate A-embedding:
* at a parameter coordinate, all coordinate A-copies agree on these
  two parts, hence agree everywhere by A-linearity of the target;
* at a constant coordinate, the coordinate A-copy agrees at the two
  parts with the line's specified constant letter, hence equals it.

The entire ambient A-copy therefore has the word coordinates of a
single line image. No claim about the ordinary girth of the power
is made, and no ambient physical A-edge is deleted.

This is a conditional geometric input. The ordered-source rigidity
lemma already in the project supplies part-preservation of ambient
power A-copies when A is finite ordered irreducible and the power
is partite over A.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {Q V : Type v}

/-- A parameter coordinate literally reads the input vertex of the
induced partite Hales--Jewett line. -/
theorem inducedHJLine_coordinate_parameter
    (A : RelStructure L Q)
    (B : StructuralRamsey.Partite.System L Q V)
    (hB : B.IsPartiteOver A)
    (N : ℕ)
    (W : HalesJewett.Line
      (StructuralRamsey.Partite.Induced.Letter A B) N)
    (i : Fin N) (hi : W.symbol i = .parameter)
    (x : V) :
    ((StructuralRamsey.Partite.Induced.lineEmbedding hB W) x).coord i = x := by
  change (StructuralRamsey.Partite.NonInduced.lineMap W x).coord i = x
  simp [StructuralRamsey.Partite.NonInduced.lineMap, hi]

/-- A constant coordinate is exactly its prescribed actual A-copy
letter, evaluated at the part of the input vertex. -/
theorem inducedHJLine_coordinate_const
    (A : RelStructure L Q)
    (B : StructuralRamsey.Partite.System L Q V)
    (hB : B.IsPartiteOver A)
    (N : ℕ)
    (W : HalesJewett.Line
      (StructuralRamsey.Partite.Induced.Letter A B) N)
    (i : Fin N)
    (c : StructuralRamsey.Partite.Induced.Letter A B)
    (hi : W.symbol i = .const c)
    (x : V) :
    ((StructuralRamsey.Partite.Induced.lineEmbedding hB W) x).coord i =
      c (B.part x) := by
  change (StructuralRamsey.Partite.NonInduced.lineMap W x).coord i =
    c (B.part x)
  simp [StructuralRamsey.Partite.NonInduced.lineMap, hi]

/-- Every genuine Hales--Jewett line embedding has A-strong image,
provided the input target is A-linear and EVERY ambient A-copy in
the induced power preserves A-parts. This needs neither A-generation
nor high girth of the HJ power. -/
theorem inducedHJLine_aStrong_of_Aparts
    (A : RelStructure L Q)
    (B : StructuralRamsey.Partite.System L Q V)
    (hB : B.IsPartiteOver A)
    (hLinear : ALinear A B.toRelStructure)
    (N : ℕ)
    (hPowerParts : ∀ e : Embedding A
        (StructuralRamsey.Partite.Induced.power B N).toRelStructure,
      ∀ p : Q,
        (StructuralRamsey.Partite.Induced.power B N).part (e p) = p)
    (W : HalesJewett.Line
      (StructuralRamsey.Partite.Induced.Letter A B) N) :
    AStrong A
      (StructuralRamsey.Partite.Induced.power B N).toRelStructure
      (copyCarrier (StructuralRamsey.Partite.Induced.lineEmbedding hB W).toEmbedding) := by
  classical
  let Power := StructuralRamsey.Partite.Induced.power B N
  let line := StructuralRamsey.Partite.Induced.lineEmbedding hB W
  intro e hNot
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hNot
  obtain ⟨u, hu⟩ := hx.1
  obtain ⟨a, ha⟩ := hx.2
  obtain ⟨v, hv⟩ := hy.1
  obtain ⟨b, hb⟩ := hy.2
  have hUa : e u = line a := hu.trans ha.symm
  have hVb : e v = line b := hv.trans hb.symm
  have huv : u ≠ v := by
    intro h
    apply hxy
    calc
      x = e u := hu.symm
      _ = e v := congrArg e h
      _ = y := hv
  have hPartA : B.part a = u := by
    calc
      B.part a = Power.part (line a) := (line.map_part a).symm
      _ = Power.part (e u) := congrArg Power.part hUa.symm
      _ = u := hPowerParts e u
  have hPartB : B.part b = v := by
    calc
      B.part b = Power.part (line b) := (line.map_part b).symm
      _ = Power.part (e v) := congrArg Power.part hVb.symm
      _ = v := hPowerParts e v
  let eI (i : Fin N) : Embedding A B.toRelStructure :=
    inducedPower_coordinateAEmbedding A B hB N e (hPowerParts e) i
  have hIparts (i : Fin N) (p : Q) : B.part (eI i p) = p :=
    inducedPower_coordinateAEmbedding_parts A B hB N e (hPowerParts e) i p
  have hCU (i : Fin N) : eI i u = (line a).coord i :=
    congrArg (fun z : StructuralRamsey.Partite.NonInduced.Vertex B N => z.coord i) hUa
  have hCV (i : Fin N) : eI i v = (line b).coord i :=
    congrArg (fun z : StructuralRamsey.Partite.NonInduced.Vertex B N => z.coord i) hVb
  obtain ⟨k, hk⟩ := W.hasParameter
  have hKU : eI k u = a :=
    (hCU k).trans (inducedHJLine_coordinate_parameter A B hB N W k hk a)
  have hKV : eI k v = b :=
    (hCV k).trans (inducedHJLine_coordinate_parameter A B hB N W k hk b)
  have hParam (i : Fin N) (hi : W.symbol i = .parameter) :
      eI i = eI k := by
    have hIU : eI i u = a :=
      (hCU i).trans (inducedHJLine_coordinate_parameter A B hB N W i hi a)
    have hIV : eI i v = b :=
      (hCV i).trans (inducedHJLine_coordinate_parameter A B hB N W i hi b)
    exact aLinear_partPreserving_twoPoint_eq A B hLinear
      (eI i) (eI k) (hIparts i) (hIparts k) u v huv
      (hIU.trans hKU.symm) (hIV.trans hKV.symm)
  have hConst (i : Fin N)
      (c : StructuralRamsey.Partite.Induced.Letter A B)
      (hi : W.symbol i = .const c) :
      eI i = c.toEmbedding := by
    have hIU : eI i u = c u := by
      calc
        eI i u = (line a).coord i := hCU i
        _ = c (B.part a) := inducedHJLine_coordinate_const
          A B hB N W i c hi a
        _ = c u := by rw [hPartA]
    have hIV : eI i v = c v := by
      calc
        eI i v = (line b).coord i := hCV i
        _ = c (B.part b) := inducedHJLine_coordinate_const
          A B hB N W i c hi b
        _ = c v := by rw [hPartB]
    exact aLinear_partPreserving_twoPoint_eq A B hLinear
      (eI i) c.toEmbedding (hIparts i) c.map_part u v huv hIU hIV
  intro z hz
  obtain ⟨p, rfl⟩ := hz
  refine ⟨eI k p, ?_⟩
  symm
  apply StructuralRamsey.Partite.NonInduced.Vertex.ext B
  · calc
      (e p).part = p := hPowerParts e p
      _ = B.part (eI k p) := (hIparts k p).symm
      _ = (line (eI k p)).part := (line.map_part (eI k p)).symm
  · intro i
    cases hi : W.symbol i with
    | parameter =>
        have heq := hParam i hi
        calc
          (e p).coord i = eI i p := rfl
          _ = eI k p :=
            congrArg (fun f : Embedding A B.toRelStructure => f p) heq
          _ = (line (eI k p)).coord i :=
            (inducedHJLine_coordinate_parameter A B hB N W i hi (eI k p)).symm
    | const c =>
        have heq := hConst i c hi
        calc
          (e p).coord i = eI i p := rfl
          _ = c p := congrArg (fun f : Embedding A B.toRelStructure => f p) heq
          _ = c (B.part (eI k p)) := by rw [hIparts k p]
          _ = (line (eI k p)).coord i :=
            (inducedHJLine_coordinate_const A B hB N W i c hi (eI k p)).symm

end StructuralRamsey.Girth
