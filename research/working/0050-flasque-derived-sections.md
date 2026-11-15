# Higher derived sections of the existing flasque sheaves

Date: 2026-11-10.

Current status: the subsequent
[0051 checkpoint](0051-singular-derived-comparison.md) proves the original
whole-complex derived comparison invertible for these flasque terms.
The remaining-comparison section below records the next step as it stood
at this checkpoint.

This completes the sheaf-term vanishing step following
[0049](0049-open-singular-sheaf-restrictions.md), within item 4 of the
[active checklist](../TARGET_BRIDGE.md). For any fixed commutative ring,
a native flasque sheaf of modules has zero positive derived sections
on every original open. Applying this to the original singular cochain
sheaves proves

\[
R^n\Gamma(U,\mathcal C^q_{\mathbb Q})=0\qquad(n>0)
\]

for every sheaf degree `q` and open `U` under the already proved
flasqueness hypotheses. The global case names the existing
`SheafHypercohomology.globalSections` functor directly. The higher
cohomology of the whole singular complex retains its previous values.

## Reusing the existing vanishing proof

`SheafCohomology.FlasqueDerived` applies the existing complete
`BasisCycles.isZero_Hobj_of_le` criterion to the collection of all
opens and all their covers. Every cover refines itself, all finite
intersections remain opens, and the existing
`FlasqueCech.isZero_cechComplex_homology_of_isFlasque` supplies positive
Čech vanishing. Thus the criterion gives actual right-derived section
vanishing, rather than stopping at Čech cohomology. The prior Stacks
01EW and 09SZ proof adaptations and their attributions are retained.
No second dimension-shifting or injective-resolution proof is added.

The generic coefficient-category theorem requires the exact underlying
abelian-sheaf functor and its injective Čech-acyclicity property. For
fixed-ring sheaves these are discharged by the existing
`LinearCoefficients.underlying` and `cechAcyclicInjectives`. Native
flasqueness passes to this same underlying sheaf because the original
restriction functions remain surjective.

`LinearCoefficients.cohomologyForgetIso` compares ordinary module-valued
derived sections with their underlying abelian groups. Both sides use
the same actual injective resolution in the original module coefficient
category. No claim that scalar forgetting preserves injective abelian
sheaves is needed. Faithfulness reflects the resulting zero object
back to the original module-valued cohomology.

The general theorem holds on any topological space. No separation,
local compactness, countability or paracompactness assumption is needed
once native flasqueness is given.

## Shared ownership and compatibility

The original `BoundedBelowDerived.rightDerivedPostcomposeIso` moves
unchanged to `SheafCohomology.DerivedPostcompose`. Its namespace and
public name remain available through the original de Rham entry point.
Betti now uses the same comparison through the shared layer, without
importing de Rham.

The previous `SchemeDeRham.moduleCohomologyForgetIso` delegates to the
general shared comparison. Its old public name and endpoints are
retained. The underlying abelian-sheaf functor declares the native site
category explicitly, retaining the same sections and maps and avoiding
a separate copy for the new consumer. The old de Rham scalar-forgetting
wrapper reuses its additive instance as well. Affine acyclicity imports
the original forms sheaf owner directly and no longer needs the
bounded-below hypercohomology module merely to access coefficient
forgetting.

## Original singular terms and canonical examples

`SingularSheafAcyclicity` applies the shared theorem to the same
`SingularCochains.cochainSheaf X q` from the original resolution.
`isZero_cochainSheaf_cohomology_of_open_paracompact` uses the existing
all-open paracompactness flasqueness theorem. The locally compact
second-countable Hausdorff specialization uses the already proved
flasque property, with canonical scheme wrappers retaining those
explicit topology hypotheses.

The canonical affine spaces in all dimensions and the original glued
P¹ satisfy these hypotheses. The existing noncompact canonical affine
chart of P¹ is tested on its original open, reusing the same fixture
from 0049. Native skyscrapers provide a separate coefficient test on
arbitrary spaces, including integer coefficients. The original nonzero
P¹ singular degree-two generator is retained as a control distinguishing
sheaf-term vanishing from total cohomology.

## Remaining comparison

Next prove that the existing bounded-below underived-to-derived
comparison is invertible for the original singular sheaf complex, using
the termwise vanishing just established. This needs the complex-level
acyclic-terms argument; no comparison isomorphism is introduced as a
premise. The native derived target and comparison already exist.

Then combine that result with the existing global-unit quasi-isomorphism
and the local rational constant-sheaf resolution. General scheme point
topology, complex coefficients, proper algebraic/analytic comparison,
general periods, purity and prescribed-class Chow coverage retain their
earlier open scope. There are no new axioms, proof placeholders,
external proof ports or dependencies.

## Verification

`make check-flasque-derived` includes the earlier open, global-unit,
cover and native-kernel checks. The new controls cover arbitrary native
skyscrapers, integer coefficients, real opens, all canonical affine
dimensions including zero, P¹, its same noncompact affine chart, and the
empty space, with arbitrary sheaf and positive derived degrees. A
compatibility check identifies the old de Rham public comparison with
the shared one, and the original P¹ total degree-two class remains
nonzero.

The combined focused verification passes all 46 standard-three axiom
checks, including the 27 open-restriction checks and 19 derived-vanishing
checks, with no errors or warnings. All 108 import-layer guards pass;
local documentation links and `git diff --check` pass. Full `lake build`
passes with 5,254 jobs. The combined root-import regression passes all
447 standard-three axiom checks and 65 export checks, with no errors or
warnings. The axiom whitelist remains `propext`, `Classical.choice` and
`Quot.sound`.
