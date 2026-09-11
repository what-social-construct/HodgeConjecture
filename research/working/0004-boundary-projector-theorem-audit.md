# Boundary projector theorem audit

Status: open research program; not a theorem or publication claim.

Audited: 2026-09-11.

## Proposal retained as an open target

The proposed headline is worth retaining as a working research target:

> **Boundary-unramified collision projector program.**  Let \(X/\mathbf C\)
> be smooth and projective, and let a correspondence be finite and
> generically etale over \(X\).  Suppose its generic sheet decomposition has
> a rational idempotent \(e_\eta\).  Under precise codimension-one
> unramifiedness, inertia, and purity hypotheses, construct
>
> \[
> \Pi_e\in CH^{\dim X}(X\times X)_{\mathbf Q},
> \qquad \Pi_e\circ\Pi_e=\Pi_e,
> \]
>
> and identify its Betti action with the independently prescribed
> cohomological projector selected by \(e_\eta\).

The intended slogan remains

\[
\text{generic projector}
+\text{ boundary-unramified extension data}
\Longrightarrow
\text{Chow projector}.
\]

This is an open program, not a consequence currently proved by the
repository.  In particular, “trivial inertia,” “vanishing different,”
“vanishing boundary defect,” and “existence of a Chow-idempotent extension”
are not interchangeable without additional theorems and hypotheses.

## The three algebras must remain distinct

The proposal currently passes through three different multiplications.
Conflating them would make the desired conclusion circular.

### 1. Pointwise generic-sheet algebra

For a marked subgroup \(H\leq G\), the generic sheet algebra is modeled by

\[
F=k^{G/H}
\]

with pointwise multiplication.  Its basic idempotents are characteristic
functions of subsets of \(G/H\).  The marked selector

\[
q=\mathbf 1_{\{H\}}
\]

is constructed in `Boundary/Sheets/GenericProjector.lean`, and the
normal-closure tensor evaluation sends the diagonal/separability element to
this selector in `Boundary/Normalization/SelectorComparison.lean`.

Multiplication by \(q\) is `diag(1,0)` in selector/CRT coordinates and a
graph-shaped operator in constant-unit coordinates.  This is the formal
A11b calculation in `Boundary/Sheets/MarkedBlockProjector.lean` and
`Realization/Chow/GaloisMarkedBlock.lean`.  It is pointwise algebra and
rational linear algebra, not Chow convolution.

### 2. Group and Hecke convolution algebras

The rational group algebra \(\mathbf Q[G]\) and the Hecke corner

\[
e_H\mathbf Q[G]e_H,
\qquad
e_H=|H|^{-1}\sum_{h\in H}h,
\]

use convolution.  A deck action sends group-basis elements to graph spans
and carries supplied idempotents to idempotents of the finite-etale free
correspondence algebra.  This is formal in
`Correspondence/FiniteGroupProjector.lean`,
`Correspondence/GroupAlgebraProjector.lean`, and
`Correspondence/HeckeProjector.lean`.

The generic characteristic function \(q\in k^{G/H}\) is not the subgroup
average \(e_H\in\mathbf Q[G]\).  `Boundary/AveragingAction.lean` compares how
the graph average acts on sheet functions under an explicit compatibility
hypothesis; it does not identify the two algebras.

### 3. Chow-convolution algebra

For a smooth projective \(d\)-fold, the desired target is

\[
CH^d(X\times X)_{\mathbf Q}
\]

with refined-intersection composition and diagonal unit.  The repository
contains abstract interfaces named `FiniteEtaleAlgebraModel`,
`RationalChowCorrespondenceModel`, and
`PresentedRationalChowCorrespondenceModel`.  None is instantiated by an
actual Chow group.  The finite-etale free algebra is explicitly a formal
span algebra and does not impose rational equivalence or refined
intersection.

Thus the formal implication

\[
e^2=e\text{ in }\mathbf Q[G]
\Longrightarrow
\Gamma(e)^2=\Gamma(e)
\]

currently ends in the free graph-span algebra.  Reaching a Chow idempotent
requires a separately constructed convolution-compatible graph-cycle map.

## Audit of the finite-etale base case

The proposed finite-etale sanity theorem is mathematically natural:

> For a finite group acting on a smooth projective complex variety \(Y\), a
> rational group-algebra idempotent \(e=\sum_g a_g g\) should give
> \(\Pi_e=\sum_g a_g[\Gamma_g]\), an idempotent Chow correspondence.

The repository proves the span-algebra version for every supplied
idempotent; it does not prove the displayed membership in
\(CH^{\dim Y}(Y\times Y)_{\mathbf Q}\).  It also has no central-idempotent,
primitive-idempotent, character, or isotypic-component theorem.  Centrality
is unnecessary for idempotence.  It becomes relevant when proving that the
image commutes with the \(G\)-action.  A general central idempotent selects a
sum of rational isotypic components; a single isotypic component requires an
appropriate primitive central idempotent or a separately specified
representation-theoretic block.

The cover hypotheses are also not encoded by the historical name
`FiniteDeckAction`: that type is only a group homomorphism into
automorphisms over the base.  `GaloisCollisionDecomposition` supplies an
explicit torsor comparison and, with `[IsFinite f]` and `[IsEtale f]`, proves
the conditional full graph-sum calculation A8.  It neither constructs the
comparison for every Galois cover nor treats arbitrary central idempotents in
Chow.

## Exact remaining inputs

### Geometric and Chow inputs

1. Specify an actual smooth projective complex variety or a named family,
   its dimension, and the finite or generically finite correspondence.
2. Construct the relevant Chow groups with rational coefficients and the
   refined-intersection correspondence product.
3. Send an admissible graph span to its fundamental cycle class and prove
   that graph composition agrees with Chow convolution, with the diagonal as
   unit and finite unions as sums.
4. For the generically separated situation, construct the normalization,
   the dense-open restriction map on correspondence classes, and a raw
   closure of the selected generic components with the required support and
   codimension.
5. Define the boundary idempotence defect
   \(\overline e_\eta^2-\overline e_\eta\) in the actual Chow-convolution
   algebra and prove that it is boundary-supported.

### Ramification, purity, and extension inputs

6. Instantiate the now-canonical conjugate normalization legs against the
   chosen boundary valuations by proving `ConjugateCenterRealization` and
   `ConjugateRamificationRealization`, then prove the application-specific
   `ConjugateBoundarySeparation` condition.  The formal endpoint already
   turns these data and visible formal unramifiedness into
   `NoCodimensionOneRamification`.
7. Use Paper I's prime-inertia and localization results with their exact
   hypotheses.  The fixed-prime-inertia unramifiedness theorem corresponding
   to Stacks Tag `0BST` remains an explicit source input in the Lean path.
8. Prove the needed all-boundary extension or purity theorem.  Existing
   structures such as `GaloisProjectorExtensionPurity`,
   `BoundarySubgroupProjectorExtension`, and
   `CompactifiedSubgroupProjectorExtension` package this conclusion as a
   field; they do not establish it for a compactification.
   Stacks Tag `0BMB` is not a dependency for this step: its pointwise
   regularity, dimension, quasi-finiteness, and specialization hypotheses do
   not directly match the present packaged global interface.
9. Prove that the resulting global class remains idempotent.  Extending a
   finite-etale cover or taking the closure of a cycle does not by itself
   kill a boundary-supported convolution defect.
10. If an obstruction \(\operatorname{ProjObs}_\partial(e_\eta)\) is
    introduced, construct its target group and prove both directions of the
    claimed vanishing criterion.  No such canonical obstruction currently
    exists in the repository.

### Realization and Hodge inputs

11. Construct Betti cohomology and its rational Hodge structures, degree by
    degree, together with the cycle-class action of Chow correspondences.
12. Fix covariant versus contravariant conventions and prove whether
    \(\Gamma_g\) acts by \(g_*\), \(g^*\), or \(g^{-1*}\).  If necessary, pass
    to the opposite correspondence algebra.
13. Prove the action is multiplicative and that codimension-\(d\)
    correspondences act by morphisms of rational Hodge structures.
14. For the marked route, construct the residual map
    \(\theta:E\to H^{2p}(X,\mathbf Q)\) geometrically at the Chow or motivic
    level, prove \(\theta(q-1)=\alpha\), and prove the action-intertwining
    square used by `MarkedGaloisSelectorComparison`.  An arbitrary rational
    linear map is insufficient.
15. Construct the Tate-augmented correspondence algebra for
    \(\mathbf Q(-p)\oplus h(X)\), including the lower-left Chow-block
    construction and detection maps and the compatibility between Hodge
    classes and Hodge morphisms.
16. To state an actual partial Hodge result, prove coverage for a named
    variety, family, or independently specified Hodge subspace.  The
    class-dependent coverage and strong replacement predicates in C5b have
    no instances.

## What the existing conditional endpoints do

`AlgebraProjectorExtension` and the Galois extension structures correctly
separate the generic and compactified algebras.  Once an extension element is
supplied, its idempotence and generic restriction are available by fields.
`PrescribedChowProjectorLift` additionally stores the equality with an
independently prescribed cohomological operator.

The closure stage is now separated one step earlier by
`AlgebraProjectorClosure`.  For any raw closure class, Lean proves that the
convolution defect `Π * Π - Π` restricts to zero.  This is only membership in
the kernel of generic restriction, not a theorem that the defect is supported
on a geometrically defined boundary or vanishes in Chow.  Zero-defect
witnesses recover `AlgebraProjectorExtension`.

There is also a clean sufficient route through
`CompactifiedDeckGraphComparison`: if generic and compactified deck actions,
their graph-cycle algebra maps, and the restriction square are supplied, an
idempotent of `ℚ[G]` has a compactified idempotent image with the prescribed
generic restriction.  This derives defect zero rather than assuming it, but
constructing the compactified action and graph-cycle square remains geometric
input.

The Jacobian-derived normalization geometry has likewise been duplicated and
adapted rather than imported.  `ConjugateNormalization.lean` constructs the
canonical right-coset-invariant conjugate legs, and
`ConjugateBoundary.lean` constructs their boundary ideals and the
fixed--moving separation predicate.  Its final theorem derives only
codimension-one unramifiedness from explicit center, ramification, visible,
and separation inputs.  New wrappers use the resulting empty ramified-point
family to discharge the local side of the selector and subgroup-projector
extension criteria.  They do not assert the separation input or a purity
theorem; the actual gluing packages remain supplied.

The newer C5b endpoint is sharper.  From a supplied compactified marked
selector, residual map, and intertwining square it detects the lower-left
class; with surjectivity it identifies the whole action with the canonical
Tate graph projector.  These are valid conditional implications.  They do
not construct the extension, residual map, comparison square, Chow detection
map, or coverage witness.

## Honest staged theorem statements

### Available formal theorem

> A deck action transports every supplied rational group-algebra idempotent
> to an idempotent in the finite-etale free graph-correspondence algebra.  A
> marked normal closure supplies the formal sheet selector and its exact
> diagonal/graph block descriptions.

This is appropriate for Paper II.

### Conditional Chow theorem

> Suppose a concrete Chow-correspondence algebra, a convolution-compatible
> graph-cycle map, and its Betti realization have been constructed.  Then the
> image of any group-algebra idempotent is a Chow idempotent, and its Betti
> action is the image of that idempotent under the induced group-algebra
> action.  If the idempotent is central, its image and kernel are
> \(G\)-stable; if it is primitive central, a separate representation theorem
> may identify its image with the corresponding rational isotypic summand.

This is an honest interface theorem, but it adds no concrete Chow instance.

### Desired boundary theorem

> For a specified generically finite correspondence and compactification,
> prove from named codimension-one unramifiedness and purity hypotheses that
> the marked generic selector admits an idempotent Chow extension whose Betti
> action equals a separately specified projector.

This remains open.  It becomes a partial Hodge theorem only after the target
projector is tied non-circularly to a named class of rational Hodge classes
and coverage is proved for that class.

## Claims excluded at the current stage

- “A boundary-unramified collision projector is algebraic” as an
  unconditional theorem.
- “The generic sheet selector equals the subgroup graph average.”
- “The finite-etale free correspondence algebra is a Chow algebra.”
- “The repository constructs
  \(\Pi_e\in CH^{\dim Y}(Y\times Y)_{\mathbf Q}\).”
- “The cohomological range is an isotypic Hodge summand” without central or
  primitive-central representation data and a concrete Hodge realization.
- “A partial proof of the Hodge conjecture” without a concrete new family or
  Hodge subspace for which all remaining inputs and coverage are proved.
