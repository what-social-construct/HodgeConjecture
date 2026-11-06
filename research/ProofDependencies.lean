-- This dependency audit loads private imported proof bodies (legacy import mode).
import HodgeConjecture.Realization.Betti.Examples.SplitGaloisAction
import HodgeConjecture.Realization.Chow.GaloisHodgeTarget
import Solution
import Lean.Util.CollectAxioms
import HodgeConjecture.MathlibCompat.DeclarationDependencies

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Declaration dependencies of selected proof endpoints

Run with `lake env lean research/ProofDependencies.lean`.

This research diagnostic traverses Lean's checked constant declarations using
a traversal of statement types and checked bodies, retaining every visited
declaration independently of Lean's cached axiom collector.
It inspects statement types and proof/definition bodies transitively, then
reports the originating `HodgeConjecture.LinearAlgebra` modules. Importing a
module alone does not count as using one of its declarations.

These are dependencies of the current formal declarations, not claims of
mathematical necessity or minimal imports. A refactored proof could have a
different closure. Assertions therefore record the current architectural
boundary; a mismatch requests review, not automatic deletion or adoption of
the new result. Generated declaration counts are deliberately not asserted.

The final two reports check supporting declarations separately: absence
from the six primary endpoint closures does not mean a utility is globally
unused. This file is a diagnostic, not part of the library's proof spine.
-/

open Lean Elab Command

meta section

namespace HodgeConjecture.Research.ProofDependencies

/-- The module that supplied an imported constant. -/
private def origin (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx]!
  | none => Name.anonymous

/-- Whether a declaration originates in the audited utility directory. -/
private def fromLinearAlgebra (env : Environment) (n : Name) : Bool :=
  (`HodgeConjecture.LinearAlgebra).isPrefixOf (origin env n)

/-- Origin modules of all transitive constant dependencies, including types. -/
private def linearAlgebraModules (env : Environment) (endpoint : Name) : List Name :=
  let declarations := (declarationDependencies env endpoint).toList.filter (fromLinearAlgebra env)
  let modules := declarations.foldl
    (fun acc n => acc.insert (origin env n)) ({} : NameSet)
  modules.toList.mergeSort (fun a b => decide (a.toString ≤ b.toString))

/-- Six primary endpoints and their expected utility-module sets. -/
private def primaryEndpoints : List (Name × List Name) := [
  (`HodgeConjecture.SplitGaloisMarkedComparison.palomarTargetSquare,
    [`HodgeConjecture.LinearAlgebra.BlockGraphProjector,
     `HodgeConjecture.LinearAlgebra.MarkedAugmentedAlgebra,
     `HodgeConjecture.LinearAlgebra.UniversalIdempotentAlgebra]),
  (`HodgeConjecture.SplitGaloisMarkedComparison.markedEmbedding_action,
    [`HodgeConjecture.LinearAlgebra.BlockGraphProjector,
     `HodgeConjecture.LinearAlgebra.MarkedAugmentedAlgebra]),
  (`HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift.rationalHodgeConjectureAt_of_classIndexedFiniteCoverGraphCoverage,
    [`HodgeConjecture.LinearAlgebra.BlockGraphProjector]),
  (`HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift.rationalHodgeConjectureAt_iff_classIndexedFiniteCoverGraphCoverage,
    [`HodgeConjecture.LinearAlgebra.BlockGraphProjector]),
  (`HodgeConjecture.Palomar.fixedPoints_heightOne_contraction, []),
  (`HodgeConjecture.Palomar.heightOne_fixedRing_unramified_descent, [])]

/-- Supporting positive examples, reported without a fixed module-set contract. -/
private def supportingEndpoints : List Name := [
  `HodgeConjecture.MarkedSheetProjector.selectorAlgebraDecomposition,
  `HodgeConjecture.SplitChowCorrespondence.spanQuotientEquiv_ofSchemeSpan]

run_cmd do
  let env ← getEnv
  for (endpoint, expected) in primaryEndpoints do
    unless env.contains endpoint do
      throwError "Missing primary endpoint {endpoint}"
    let actual := linearAlgebraModules env endpoint
    unless actual.all expected.contains && expected.all actual.contains do
      throwError "Dependency boundary changed for {endpoint}\nExpected: {expected}\nActual: {actual}"
    logInfo m!"PASS {endpoint}\n  LinearAlgebra modules: {actual}"
  for endpoint in supportingEndpoints do
    unless env.contains endpoint do
      throwError "Missing supporting endpoint {endpoint}"
    let actual := linearAlgebraModules env endpoint
    logInfo m!"SUPPORT {endpoint}\n  LinearAlgebra modules: {actual}"

end HodgeConjecture.Research.ProofDependencies
