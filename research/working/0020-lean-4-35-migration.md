# Lean 4.35 migration

Status: migrated and validated in the working tree (2026-11-05).

The dependency pair is Lean `leanprover/lean4:v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` (the `v4.35.0` release).
This supersedes the Lean 4.24 / Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`
baseline recorded in the Axiom Stacks reuse audit.

The migration was validated in an isolated copy of the complete
working tree, including the existing uncommitted cycle and realization work.
The source files adopt Lean's module syntax with public imports and exposed
public definitions, preserving the existing public API and definitional
computations. The package retains the older elaborator's transparency
behavior through the two `backward.isDefEq.respectTransparency` options;
these options do not alter kernel checking.

The port uses the current Mathlib étale and smooth classes, native ideal
heights, automorphism wrappers, monoid-algebra coefficient equivalences,
localized-module operations, and standard topological simplices. In
particular, the normalization interfaces retain their original ideal-power
ramification index, now named `Ideal.ramificationIdx'`; the new unprimed
index is a different definition and is not substituted for it.

The standalone axiom allowlists now use Lean's public `collectAxioms` API.
The three declaration-dependency audits deliberately retain legacy import
mode to load private imported proof bodies; ordinary module imports expose
statement information and cached axiom reports but omit those bodies.
Their traversal still checks types and checked proof/definition bodies and
retains the original expected dependencies and forbidden-branch assertions.

The bounded Axiom adaptation identifies actual fiber residue fields with
the original structural scalar actions. The new finite-fiber map and
computed degree law act on the existing cycle module, including coefficients
with zero divisors. Principal-relation preservation, Chow descent and the
constant locally free rank comparison remain open.

The Axiom snapshot remains independently pinned by the reuse audit. Its
statements are proof references, not assumed inputs to this migration.
No realization gap or conditional geometric hypothesis is discharged by
changing the toolchain.

Validation in the migration copy: the existing full default build passed
(3670 jobs), the new finite-fiber target passed, and all 52 current research
verification/diagnostic files passed. The integrated file retains 1255
`#check` declarations, 565 examples and 1147 axiom reports. Observed theorem
axioms are within `propext`, `Classical.choice` and `Quot.sound`.
The production source scan contains no proof placeholders or new axiom
commands; the two intentional `Challenge.lean` statement placeholders remain.
Native style and deprecation warnings remain under Lean 4.35.

After applying the migration, the full working-tree `lake build` passes
(3676 jobs). All 52 research files byte-match their checked migration-copy
sources. Documentation file/heading links and exact dependency/JSON checks
pass. `lake env lean research/Verification.lean` also passes from the actual
working-tree location, with all reported theorem axioms within the same
standard-three allowlist. `git diff --check` passes. The original sources
and Lean 4.24 cache were preserved in a local backup before applying the port.
Clean-clone, Comparator/NanoDa, manuscript rendering and human mathematical
review are outside these checks.
