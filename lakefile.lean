import Lake

open Lake DSL

package «hodge-conjecture» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-!
Pin Mathlib directly so fresh clones reproduce the verified dependency graph.
-/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib HodgeConjecture

@[default_target]
lean_lib Challenge where
  roots := #[`Challenge]

@[default_target]
lean_lib Solution where
  roots := #[`Solution]
