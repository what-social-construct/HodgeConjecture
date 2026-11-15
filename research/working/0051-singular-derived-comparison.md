# The original whole-complex derived comparison

Date: 2026-11-10.

Current status: the subsequent
[0052 checkpoint](0052-rational-singular-constant-sheaf-comparison.md)
assembles the global unit, this comparison and the local resolution into
the actual rational singular/constant-sheaf cohomology isomorphism. The
remaining-work section below records the scope at this checkpoint.

This completes the whole-complex comparison step following
[0050](0050-flasque-derived-sections.md), within item 4 of the
[active checklist](../TARGET_BRIDGE.md). For a bounded-below complex of
native flasque sheaves of modules over a fixed commutative ring, the
existing derived-functor unit is invertible. Its nonnegative specialization
proves that the original map

\[
\Gamma(X,\mathcal C^\bullet_{\mathbb Q})
\longrightarrow R\Gamma(X,\mathcal C^\bullet_{\mathbb Q})
\]

is an isomorphism in the existing bounded-below derived category, under
the already proved flasqueness hypotheses. The induced original comparison
on homology is an isomorphism in every integer degree. This is a statement
about the entire original complex, with its existing differential.

## Shared ownership

The generic construction moves unchanged from
`Realization.DeRham.SheafHypercohomology` to
`SheafCohomology.Hypercohomology`. The original public namespaces and names
are retained, including the derived target, comparison, homology maps,
naturality and injective-resolution comparisons. The old de Rham entry
point publicly imports this owner and retains the original scheme
de Rham wrappers. Betti imports the shared owner without importing
de Rham geometry or forms.

There is no new derived target, replacement comparison, cochain model or
assumed comparison isomorphism. The original fixed-ring module coefficient
category, global-sections functor and nonnegative extension are retained.

## Bounded-below exactness

`SheafCohomology.FlasqueComplex` proves the complex-level input. For an
acyclic bounded-below complex of abelian sheaves with native flasque terms,
the native cycle objects are flasque. The induction starts from a zero
cycle below the lower bound and uses the original differential's native
factorization through the next cycle object. The resulting cycle short
complex is short exact.

Pinned Mathlib's `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`
supplies flasqueness of the quotient cycles. Its `epi_of_shortExact`
supplies actual surjectivity on sections. Native kernel preservation and
these epimorphisms prove that the original sections complex is acyclic,
on every original open. No compactness or finite cover is required.

This uses the stronger native flasqueness established in 0049, whose
positive derived vanishing was proved in 0050. It avoids adding an ordinary
derived-functor long exact sequence or a second resolution construction
merely to prove this comparison for flasque terms. A theorem for arbitrary
acyclic terms without flasqueness is not claimed here.

## The original unit

`SheafCohomology.FlasqueHypercohomology` uses pinned Mathlib's
`CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective`.
After applying the existing exact underlying-abelian-sheaf functor, the
native monomorphic injective replacement has its native cokernel
sequence. Its quotient is acyclic, bounded below, and has flasque terms.
The preceding section argument shows that its sections remain acyclic.
The original replacement map therefore remains a quasi-isomorphism on
sections, by its actual long exact homology sequence.

Exact scalar forgetting uses the existing `LinearCoefficients.underlying`
functor and reflects the original module-valued sections comparison.
Underlying sheaves of the injective replacement terms are flasque by the
existing instance; scalar forgetting is not assumed to preserve injectives.

Naturality of the existing derived-functor unit and its already proved
invertibility on complexes of injectives then prove invertibility on the
original complex. Extension by zero retains the original nonnegative
terms, and its negative terms are native zero sheaves. The exported
homology isomorphism has exactly the original comparison as its hom map.

## Singular terms and remaining work

`Betti.SingularSheafHypercohomology` applies this result to the original
singular sheaf complex. Hausdorff spaces with all opens paracompact suffice;
the locally compact second-countable Hausdorff specialization reuses the
already proved native flasqueness. Canonical affine spaces in every
dimension and the original glued P¹ satisfy the hypotheses. Scheme wrappers
retain explicit point-topology assumptions.

Next compose this comparison with the existing global sheafification-unit
quasi-isomorphism and local rational constant-sheaf resolution. This will
identify the original rational singular cohomology with the actual derived
constant-sheaf target on the covered spaces. That composite is not yet
exported here. General scheme topology, complex coefficients, proper
algebraic/analytic comparison, general periods, purity and prescribed-class
Chow coverage retain their earlier open scope.

## Verification

`make check-singular-derived-comparison` adds all-degree whole-complex
controls to the earlier termwise vanishing checks. The new fixtures cover
the real line, the empty space, all canonical affine dimensions including
zero, the original P¹, integer-coefficient native skyscrapers and negative
integer degrees. The original comparison is tested by reflexive hom-map
equalities. The original nonzero P¹ total singular H² class is retained.

The focused verification passes all 30 standard-three axiom checks with
no errors or warnings. All 112 import-layer guards, local documentation
links and `git diff --check` pass. Full `lake build` passes with 5,258 jobs.
The combined root-import regression passes all 477 standard-three axiom
checks and 73 export checks, with no errors or warnings. The axiom
whitelist remains `propext`, `Classical.choice` and `Quot.sound`.
