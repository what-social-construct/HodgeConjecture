# Paper II: finite-group and marked-sheet projectors in Lean

Status: WORKING DRAFT -- not yet queued for submission.

Current author-review manuscript: [`../../paper/paper2.tex`](../../paper/paper2.tex)
([PDF](../../paper/paper2.pdf)).

## Proposed positioning

Paper II reports a machine-checked infrastructure result.  Its center is the
formal correspondence and marked-normal-closure package A1--A7 and A9--A11b
from `../CLAIM_LEDGER.md`.  It does not claim a proof, a new case, or a
reduction of the Hodge conjecture.

The supplied compactified-graph comparison A5a, conjugate-boundary endpoint
C3a, and raw closure-defect calculus C4a sharpen the boundary audit.  They
should be presented as an exact factorization of the remaining geometry, not
as a constructed Chow compactification.

The finite-etale torsor/collision comparison A8 is a conditional application,
not part of the unconditional core.  The height-one fixed-ring and inertia
results A12, A14, and A15 belong to Paper I and should be cited from
`../../paper/paper1.tex` rather than presented again as Paper II results.
The marked Chow/Hodge endpoint C5b belongs only in a conditional outlook.

## Draft abstract

We formalize in Lean 4 a correspondence calculus for schemes over a fixed
base.  Correspondences are spans and compose by fiber product; after
quotienting by span isomorphism, endocorrespondences form a monoid whose
rational monoid algebra records formal convolution.  Correspondences with
finite-etale legs form a convolution submonoid, and transpose induces a
convolution-reversing involution.  A deck action gives an algebra map from the
rational group algebra, carrying supplied idempotents and orthogonal
decompositions to formal correspondence projectors.  Finite subgroup averages
and normalized Hecke corners give explicit examples.

Given a supplied commutative square between generic and compactified graph
realizations, every group-algebra idempotent maps to a compactified idempotent
with the prescribed generic restriction.  For an arbitrary raw closure, its
convolution defect restricts to zero; actual vanishing remains an additional
condition.

For a marked finite normal closure, we construct the canonical deck action on
the affine integral-closure normalization and identify the marked intermediate
normalization with the relevant fixed ring.  Chosen quotient representatives
give evaluation maps from collision tensor algebras to functions on Galois
sheets.  The formal-unramified diagonal element maps to the marked singleton
selector; over a perfect base field, the normal-closure tensor algebra is
equivalent to the sheet-function algebra.  Multiplication by that selector is
diagonal in selector/CRT coordinates and becomes a Tate-shaped graph operator
after the canonical change to constant-unit coordinates.

Conditionally, an explicitly supplied Galois torsor decomposition and
finite-additive realization identify the normalized self-fiber-product class
with the full-group average.  We keep the pointwise sheet algebra, the
group/Hecke convolution algebra, and any future Chow-convolution algebra
distinct.  No concrete Chow realization, compactified extension, or
identification with a prescribed Hodge projector is asserted.

## Paper II theorem package

The public theorem inventory is deliberately partitioned.

- **Formal correspondence core (A1--A7).**  Span composition, strict
  isomorphism classes, the finite-etale convolution algebra, transpose,
  transport of group-algebra idempotents, finite averages, and normalized
  Hecke corners.
- **Formal marked-normal-closure core (A9--A11b).**  The canonical deck
  action on the normalization, the fixed-ring description of the marked
  intermediate normalization, the collision-to-sheet evaluation maps and
  marked selector, and the selector/CRT-to-graph block calculation.
- **Conditional finite-etale application (A8).**  The graph-sum and
  normalized-collision statements must begin with “given an explicit torsor
  comparison and a `FiniteEtaleAlgebraModel`.”  Paper II does not construct
  either input for every finite-etale Galois cover.
- **Supplied compactified graph and raw-defect layer (A5a, C4a).**  A
  compatible global graph realization derives compactified idempotence and
  zero defect.  Without it, raw closure gives only a defect in the kernel of
  generic restriction.  Neither construction identifies that kernel with
  boundary-supported Chow classes.
- **Conjugate-boundary separation layer (C3a).**  Canonical conjugate
  normalization legs and their pulled-back boundary ideals are constructed
  internally.  The codimension-one endpoint still assumes the center and
  ramification realizations, visible formal unramifiedness, and the explicit
  separation condition.  It discharges the local side of the existing
  extension criteria but proves neither purity nor global étaleness.
- **Imported Paper I input (A12, A14, A15).**  Cite *Height-One Fixed-Ring
  Descent: Localization and Formal Unramifiedness* for prime inertia,
  valuation/localization comparison, and selected fixed-ring descent.  Keep
  its `0BST`-shaped fixed-inertia unramifiedness premise visible; Paper II must
  not convert that cited input into an unconditional theorem.
- **Conditional outlook (C5b).**  The marked residual comparison and
  lower-left detection endpoint may be stated as a future application, with
  every compactified extension, residual map, action square, and Chow
  detection hypothesis displayed.

A13, the abstract normalized pull--push calculation, is useful background but
is not part of the Paper II theorem spine.

The most compact unconditional mathematical endpoint is:

> A finite deck action maps every rational group-algebra idempotent to an
> idempotent in the finite-etale free correspondence algebra. For a finite
> subgroup, this map restricts to the associated normalized Hecke corner.  A
> marked finite normal closure supplies a canonical normalization action and a
> collision-tensor evaluation whose diagonal element is the marked sheet
> selector; multiplication by that selector has the explicit diagonal/graph
> block forms proved in Lean.

The A8 corollary is then stated separately:

> Given an explicit Galois torsor decomposition and a finite-additive
> realization, the normalized collision class realizes the full-group
> averaging projector.

## Relation to Paper I

Paper II may use A12, A14, and A15 to explain how the marked sheet data meet a
height-one boundary, but it should not duplicate their proofs or count them as
new Paper II results.  The citation must preserve Paper I's division between
machine-checked descent/localization and the external fixed-prime-inertia
input identified with Stacks Tag `0BST`.

In particular, Paper I does not identify the pointwise marked selector with a
graph-convolution projector and does not construct its Chow compactification.
Those are separate Paper II/outlook interfaces.

## What the note must not imply

- The formal free span algebra is not the Chow ring of correspondences.
- A rational group-algebra idempotent is not the same element as a
  characteristic-function idempotent in the pointwise sheet algebra.
- A normalized off-diagonal collision class is not generally idempotent.
- The torsor comparison is data supplied to the theorem, not constructed for
  every asserted cover by this repository.
- A8 is conditional and is not evidence for an unconditional Chow
  realization.
- A12, A14, and A15 are cited Paper I material, not a second novelty claim.
- Boundary purity, construction of the compactified graph square, geometric
  identification of the restriction kernel, raw-defect vanishing, residual
  motivic realization, and lower-left Chow detection remain interfaces.
- C5b is a conditional implication.  No coverage, replacement, or concrete
  Chow/Hodge instance is constructed.
- Equality with a prescribed Hodge projector is assumed or derived only from
  the explicitly supplied comparison square; it is not a consequence of
  group averaging alone.
- The normal-closure tensor evaluation map becomes an algebra equivalence
  under the explicit perfect-base-field hypothesis; this is a generic-field
  splitting statement, not a compactified Chow construction.

## Suggested section order

1. Span correspondences and the finite-etale free convolution algebra
   (A1--A4).
2. Deck-group and averaging projectors, followed by the supplied
   compactified-graph and raw-defect comparison (A5--A6, A5a, C4a).
3. Hecke projectors (A7).
4. Marked normal closures and fixed intermediate normalizations (A9--A10).
5. Collision tensors, sheet evaluation, and the marked block calculation
   (A11--A11b).
6. Conditional Galois collision realization (A8).
7. Relation to Paper I and the conditional Chow/Hodge outlook (C5b).

## Remaining work before queueing

- Recheck exact source mappings for A1--A11b and the cross-paper citations for
  A12, A14, and A15.
- Check nearby Lean/mathlib formalizations and mathematical literature.
- Extract a short theorem inventory with fully qualified Lean names and exact
  source lines at the release commit.
- Ensure the abstract and introduction label A8 and C5b as conditional on
  first mention.
- Add author metadata and a license.
- Obtain independent mathematical review of the prose claims.
