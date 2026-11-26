import Girth.ContactSubstitution
import Girth.TrainWagonClassRestriction
import Girth.TrainLabelledCutGirth
import Girth.TrainWagonNodeGluing
import Girth.TrainCutoffWellFounded
import Girth.RefinementRunCount
import Girth.ForestTreeRewire
import Girth.ForestJoinGlue
import Girth.ForestAuxiliaryDeletion
import Girth.ForestEnumeration
import Girth.CompletionBudget
import Girth.MixedForestInduction

/-!
# Active validation root for the contact-graph manuscript

Historical sources and checks are deliberately left in the repository,
but are not build targets on this branch.  The explicit module target
+Girth builds this root and its transitive imports only.
-/
