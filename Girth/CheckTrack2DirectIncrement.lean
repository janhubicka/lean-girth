import Girth.ForestRecursiveOutputGirth

/-!
# Track 2: audited reuse of the pre-existing direct increment

No new direct-increment proof is needed. The existing theorem
`actualPartiteDesignatedAB_forest_and_girth_of_localGeometry`
already derives local strongness for cutoffs greater than two,
the old and core linearity, and output girth-two BEFORE the
mixed-forest conclusion. It then proves output mixed forests
and full ordinary support girth through the cutoff.

This file separately checks those existing declarations.
A successful Lake build and strict printed-axiom audit are
required; no new theorem is asserted by this check file.
-/

#check StructuralRamsey.Girth.girthGT_of_finiteMixedForestThrough
#check StructuralRamsey.Girth.aStrong_of_finiteMixedForestThrough
#check StructuralRamsey.Girth.actualActiveAttachment_girthGT_two_of_mixedOld
#check StructuralRamsey.Girth.actualPartiteDesignatedAB_forest_and_girth_of_localGeometry

#print axioms StructuralRamsey.Girth.girthGT_of_finiteMixedForestThrough
#print axioms StructuralRamsey.Girth.aStrong_of_finiteMixedForestThrough
#print axioms StructuralRamsey.Girth.actualActiveAttachment_girthGT_two_of_mixedOld
#print axioms StructuralRamsey.Girth.actualPartiteDesignatedAB_forest_and_girth_of_localGeometry
