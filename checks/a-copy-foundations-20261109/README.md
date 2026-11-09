# A-copy foundations: local validation

Validated 2026-11-09 on an isolated checkout with Lean 4.35.0-rc3 and the
repository's pinned dependencies. Publication base is commit
`e3509b82fe45fd42663eee948b1a6321716752dc` on
`validation/compact-diagram-20261109`; this proposal is published separately on
`validation/a-copy-foundations-20261109`.

The local worktree was created at `2f900df5b3ee3c32e6471f143dd720bfea27781a`
and supplied with the four compact-diagram source/check pairs added by e3509b8.
It uses private copies of dependency and project build caches. The separate
ongoing validation checkout was not edited.

## Results

| Module | Checked declarations | Scope |
| --- | ---: | --- |
| `Girth/ACopyOverlapRealization.lean` | 21 | Coherent binary labels give partial bijections, exact point quotients and intersections; linearity and a nontrivial coordinate type identify nodes with their specified carrier sets; covered actual charts reconstruct their point space. |
| `Girth/ACopyExactStar.lean` | 37 | The genuinely generated equivalence has a core/private-class normal form, exact source restrictions, and injective class maps. Includes five regression declarations. |

Both new modules and both check files compile locally. The strict transitive
axiom checker allows only `propext`, `Classical.choice`, and `Quot.sound` and
passes all 58 declarations. Neither new module nor check file contains a
`sorry` or a new axiom declaration. See the paired provenance notes and logs
for commands, exports and exact assumptions. No whole-repository build was
claimed: these were targeted new-module checks. The existing Lean CI already
discovers every `Girth/**/*.lean` and `Check*.lean`, so no workflow or umbrella
import change is needed.

## Deliberate boundary

These results start validation of the diagram formulation. They do not prove
decorated relational reconstruction, irreducible-chart coverage, the combined
point/wagon instantiation, nested parent maps, the new all-cutoff local-step
package, or the full recursive Ramsey theorem. Existing conditional
certificates retain their original scope. Manuscript markers must distinguish
the checked abstract quotient facts from those remaining applications.
