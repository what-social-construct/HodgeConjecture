import Lake

open Lake DSL

package «hodge-conjecture» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`backward.isDefEq.respectTransparency.types, false⟩
  ]

/-!
Pin Mathlib directly so fresh clones reproduce the verified dependency graph.
-/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib HodgeConjecture

@[default_target]
lean_lib Challenge where
  roots := #[`Challenge]

@[default_target]
lean_lib Solution where
  roots := #[`Solution]
