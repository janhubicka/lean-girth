import Girth.TrainFillingPrivateTwoTypeOrderGirth

set_option Elab.async false

/-!
# Minimal Track 5 girth interface gate: independent old/local edge types

The old RR_h ordered edge has vertex set V(X), while the inserted
X-edges have the original smaller coloured edge type.
The two types can use DIFFERENT relational languages.

This file deliberately imports ONE new Track 5 module and its
already checked dependencies. A clean exact-head Lean build
would establish the first foundational repair without depending
on the other ~58 new Track 5 candidate modules.

Run:
  LEAN_NUM_THREADS=1 lake env lean Girth/CheckTrack5TwoTypeGirth.lean
and inspect all output, especially #print axioms.

Presence of this file is NOT evidence that the command has run.
-/

#check StructuralRamsey.Girth.TrainRecursiveWitness.OrderStage.canonicalFilledCut_fullSystemGirthGT_twoTypes

#print axioms StructuralRamsey.Girth.TrainRecursiveWitness.OrderStage.canonicalFilledCut_fullSystemGirthGT_twoTypes
