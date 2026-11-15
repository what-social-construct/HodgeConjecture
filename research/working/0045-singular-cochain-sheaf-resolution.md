# Rational singular cochain sheaf resolution

Date: 2026-11-09.

This completes the local singular-sheaf resolution following
[0044](0044-intrinsic-holomorphic-poincare.md), within item 4 of the
[active checklist](../TARGET_BRIDGE.md). It uses the existing rational
singular cochains, on the existing open-subspace topology, and the
already instantiated native sheaf category, constant sheaf and
sheafification. The full global singular/sheaf-cohomology comparison
and the complex-coefficient comparison remain open.

The subsequent [0046 checkpoint](0046-arbitrary-open-cover-small-chains.md)
now proves the arbitrary-cover small-chain/cochain comparison and
acyclicity of the original per-cover vanishing kernel. The
[0047 checkpoint](0047-global-sheafification-kernel.md) now identifies
the actual global-unit kernel with locally zero cochains and proves its
native acyclicity. The later
[0048 checkpoint](0048-global-singular-sheaf-sections.md) proves global-unit
surjectivity and its quasi-isomorphism to termwise sections on paracompact
Hausdorff spaces. Sheaf-term acyclicity and the derived-section comparison
remain open. This checkpoint's original validation record is retained below.

## The original cochains on the original opens

`Realization.Betti.SingularPresheaf` packages the existing continuous
pullbacks into a contravariant complex functor. On an open U its
`presheaf` is literally `SingularCochains.Cochain (Opens.toTopCat X).obj U n`.
Restrictions are the existing singular pullbacks along native open
inclusions. The differential and its square-zero identity are the
existing alternating-coface differential and complex identity.

`sectionComplexIso` identifies evaluation of this presheaf complex with
the original singular complex on U. `sheafComplex` applies the shared
native sheafification; there is no claim that raw singular cochains
already form a sheaf. `globalCochainsToSheaf` is the actual cochain map
from the original global complex to global sections of this sheaf
complex, using the native top-open isomorphism and sheafification unit.
Its being a quasi-isomorphism is not yet proved.

## Actual local primitives and sheaf exactness

`Geometry.LocallyContractible` proves that real normed spaces have
contractible neighborhood bases and transports these bases through the
original manifold charts. These are actual topology proofs, without
Hausdorff, countability, compactness, or supplied comparison hypotheses.

`SingularContractible.exists_primitive` extracts actual cochain primitives
from the existing proved contractible-space cohomology vanishing.
`SingularLocalExactness` restricts a closed cochain to a contractible
neighborhood, takes its primitive there, and restricts again to an open
neighborhood. Basis neighborhoods need not themselves be open. The
existing degree-zero path-connected calculation similarly proves local
constancy of closed zero-cochains.

`SingularSheafResolution.augmentation` sheafifies literal constant
zero-cochains. The shared nonempty-open injectivity criterion proves
its monomorphism. Local constancy gives degree-zero exactness; actual
local primitives give exactness in every positive degree. The shared
`AugmentedComplex` construction proves that the same constant-sheaf
map is a full quasi-isomorphism of rational sheaf complexes.

`SchemeSingularSheaves` proves the local topological hypothesis using
the existing canonical analytic atlas, then specializes this resolution
to schemes smooth of fixed relative dimension over the complex base.
No replacement point carrier, topology or comparison-data structure is
introduced. Canonical affine schemes, including dimension zero, and the
original glued projective line instantiate it.

## Shared owners, retained interfaces

`SheafCohomology.LinearSheaves` now owns the native fixed-ring
sheafification, its map on complexes, its unit on complexes, and the
existing `SheafHypercohomology.globalSections` definition. The algebraic
de Rham wrappers reuse these definitions; the public names of global
sections and the de Rham interfaces are retained.

`LocalExactness` now proves the local-lift argument once at the presheaf
stalk level. The previous sheaf exactness criterion delegates to that
proof. The native sheafification-unit stalk isomorphism gives the
corresponding criterion after sheafification. The original proof
attribution remains in that module.

`ConstantLift` now shares its local-injectivity proof between the
previous constant-sheaf lift and the sheafified presheaf augmentation.
No extra sheaf-category, constant-sheaf or derived-section implementation
is added. There are no new axioms, proof placeholders, proof ports, or
dependencies.

## Remaining global obligations

A local sheaf resolution alone does not identify the cohomology of
original global singular cochains with derived global sections.
The concrete next proof is that `globalCochainsToSheaf`, followed by
the underived-to-derived comparison, computes those derived sections.
For the intended smooth projective spaces, a classical route needs
arbitrary-open-cover small-chain comparison and the appropriate sheaf
acyclicity/global-unit argument, with its topological hypotheses proved. The indexed extension is now proved in
[0046](0046-arbitrary-open-cover-small-chains.md), reusing the original
mesh estimate and supported subdivision/homotopy operators. The actual
global-unit kernel identification and acyclicity are now proved in
[0047](0047-global-sheafification-kernel.md); global surjectivity and
sheaf-term acyclicity for derived sections remain open. Surjective restriction
maps of a presheaf alone do not prove its sheafification flasque.

The present resolution has rational coefficients. The holomorphic
resolution has complex coefficients. Their coefficient comparison must
be constructed explicitly. Tensoring rational cochains with the complex
numbers does not in general give all complex-valued cochains on an
infinite simplex set. Proper algebraic/analytic comparison, general
periods, purity and Chow coverage retain their previous open status.

## Verification

`make check-singular-sheaves` checks literal original cochain carriers,
canonical affine resolutions in all dimensions, dimension zero and the
original projective line. A discontinuous rational zero-cochain has
coboundary value one on the original oriented interval, so the control
coboundary is nonzero. Actual local exactness supplies a primitive of
this nonzero closed cochain. Distinct constants remain distinct.
The focused audit checks 27 declarations against only `propext`,
`Classical.choice` and `Quot.sound`.

The focused verification passed all 27 audits without warnings or errors.
The import-boundary guards, local documentation links and whitespace check
also passed. The full `lake build` passed all 5,230 jobs. Existing
repository warnings retain their prior scope; the focused verification
has no warnings or errors.

The combined root-import regression passed 192 standard-three axiom audits
and 28 public-export checks, with no warnings or errors. This includes
the existing coordinate Poincaré/Kähler, analytic-atlas, forms-descent
and intrinsic Poincaré checks alongside the new singular sheaf checks.
Builders ran sequentially before the root regression.
