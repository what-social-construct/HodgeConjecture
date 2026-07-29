# Hodge Conjecture / Collision Projectors

This Lean project develops collision ideals as scheme-theoretic lifts of
correspondence decompositions, with boundary ramification and inertia measuring
the failure of generic idempotents to extend.

The initial formalization reuses the sibling `collision-ideals` project and
adds:

- an abstract tensor-product collision algebra `A ⊗[B] A`;
- the diagonal obstruction and residual annihilator;
- the square-zero overlap defect;
- the contact quotient;
- the equivalence between vanishing defects and an idempotent decomposition.
- the Noether different and its canonical contact-quotient equivalence;
- the identification of the ramification locus with the support of relative
  Kähler differentials;
- the height-one comparison with the Dedekind different, kept as an explicit
  local hypothesis, and the resulting description of its zero locus as the
  ramification locus;
- the resulting boundary criterion: the generic base-sheet selector extends
  exactly when the collision different avoids the boundary prime, once the
  local different and inertia realizations are supplied;
- the canonical Chinese-remainder product decomposition
  \[
  C \cong (C/J)\times(C/\operatorname{Ann}(J))
  \]
  when the overlap and contact defects vanish;
- the induced homeomorphism of prime spectra and an actual affine-scheme
  isomorphism with the disjoint union of the diagonal and residual quotient
  schemes;
- an explicit correspondence-realization interface carrying
  scheme-theoretic idempotents to idempotent endomorphisms of a cohomology
  module;
- complementary image/kernel decompositions for the realized projector,
  including a separate splitting of every preserved bigraded piece;
- a boundary selector-extension interface and the theorem that a realized
  bigraded projector exists exactly when the collision different avoids the
  chosen boundary prime.

The formalized implication chain is therefore:

\[
\text{vanishing collision defects}
\Longrightarrow
\text{product ring and affine-scheme decomposition}
\Longrightarrow
\text{cohomological projector},
\]

with boundary inertia controlling existence of the extended selector used in
the final arrow.

The remaining work is geometric rather than hidden in the formalization.  For
a concrete compactification one must supply:

1. the local comparison between the collision Noether different and the
   valuation-theoretic different;
2. the realization of ramification by relative inertia in a Galois closure;
3. the actual boundary extension object carrying the idempotent selector;
4. the proper algebraic cycle or correspondence and its action on the desired
   Chow, motivic, or Hodge realization.

Mathlib does not yet provide a general Chow-correspondence or Hodge-structure
library.  The project therefore isolates those later constructions behind
explicit interfaces instead of treating them as already available.
