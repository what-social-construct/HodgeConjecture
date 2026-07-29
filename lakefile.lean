import Lake

open Lake DSL

package «hodge-conjecture» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-!
During the initial development, reuse the formally verified collision and
inertia machinery from the sibling project.  This keeps the new project
focused on the decomposition-defect and correspondence layers.
-/
require «collision-ideals» from "../collision-ideals"

@[default_target]
lean_lib HodgeConjecture
