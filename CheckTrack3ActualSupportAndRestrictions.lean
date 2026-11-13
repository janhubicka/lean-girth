import Girth.TrainActualASupportTrainTransport
import Girth.TrainGeneratedActualAllLevelRestriction

/-!
# Numbered Track 3: actual A-support and exact generated restrictions

The complete physical A-copy carrier pushout, all-level train transport,
and exact generated standard/core restrictions are distinct from the
cycle-preservation theorem. All five endpoints are source-only and
conditional on their printed hypotheses.

This file adds the previously missing direct strict-axiom gate for
Girth.TrainGeneratedActualAllLevelRestriction. It does not introduce
new theorems, claim a fresh compilation or promote manuscript markers.

Manuscript parent: janhubicka/girth@8c9cfa6e (published 41-page draft).
See janhubicka/lean-girth issue #1054.
-/

#check @StructuralRamsey.Girth.actualACarrierPushoutEquiv
#check @StructuralRamsey.Girth.actualAttachedATrain_rel_iff
#check @StructuralRamsey.Girth.actualAttachedATrain_wagonCarrier_eq
#check @StructuralRamsey.Girth.generatedActualASupportTrain_restrict_standard
#check @StructuralRamsey.Girth.generatedActualASupportTrain_restrict_core

#print axioms StructuralRamsey.Girth.actualACarrierPushoutEquiv
#print axioms StructuralRamsey.Girth.actualAttachedATrain_rel_iff
#print axioms StructuralRamsey.Girth.actualAttachedATrain_wagonCarrier_eq
#print axioms StructuralRamsey.Girth.generatedActualASupportTrain_restrict_standard
#print axioms StructuralRamsey.Girth.generatedActualASupportTrain_restrict_core
