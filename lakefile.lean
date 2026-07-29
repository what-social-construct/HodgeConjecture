import Lake

open Lake DSL

package «hodge-conjecture» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-!
Reuse the formally verified collision and inertia machinery at a pinned
revision so fresh clones reproduce the same dependency graph.
-/
require «collision-ideals» from git
  "https://github.com/what-social-construct/collision-ideals.git" @
  "a409db9922279907493d96f691b5ea9eb71baaf9"

@[default_target]
lean_lib HodgeConjecture
