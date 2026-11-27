import Girth.ContactValidation
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

The default target includes the final relational and unordered hypergraph
theorems, together with the reused regression imports below. Historical sources
and checks are deliberately left in the repository but are not build targets
unless imported here. Both `lake build` and the explicit module target `+Girth`
build this root and its transitive imports.
-/
