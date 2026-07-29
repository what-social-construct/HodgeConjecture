# Hodge Conjecture / Collision Projectors

This Lean project develops collision ideals as scheme-theoretic lifts of
correspondence decompositions, with boundary ramification and inertia measuring
the failure of generic idempotents to extend.

The formalization reuses a pinned revision of the `collision-ideals` project
and adds:

- locally owned, dimension-independent copies of the foundational
  collision modules:
  - `Diagonal`, `Basic`, and `CollisionDiagonal` for
    \(I_\Delta\), \(I_R\), \(\mathcal O\!bs=I_\Delta/I_R\), and the quotient
    diagonal map;
  - `OffDiagonal` for the colon residual, saturation, clopen idempotents,
    complementary ideals, and the Chinese-remainder decomposition;
  - `FiberProduct`, `UniversalProperty`, and `PolynomialFiberProduct` for
    the canonical equivalence between the collision quotient and
    \(A\otimes_B A\);
  - `GaloisSheets`, `InertiaQuotient`, and `DecompositionSheets` for the
    dimension-independent sheet action and inertia indices;
- an abstract tensor-product collision algebra `A ⊗[B] A`;
- the diagonal obstruction and residual annihilator;
- the square-zero overlap defect;
- the contact quotient;
- the equivalence between vanishing defects and an idempotent decomposition;
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
  chosen boundary prime;
- a compactification/purity interface for an arbitrary family of height-one
  boundary components, proving that a global projector exists exactly when
  the collision different avoids every boundary prime;
- a Chow-style presentation by a raw cycle ring modulo a
  rational-equivalence ideal;
- the canonical descent of the raw cycle action to the quotient, including
  the theorem that rationally equivalent cycles act identically;
- the combined compactified Chow and Hodge-style bigraded projector criterion
  \[
  \bigl(\exists\text{ global bigraded Chow projector}\bigr)
  \iff
  \forall i,\quad
  \mathfrak D_{\mathrm{coll}}\not\subseteq P_i.
  \]
- local copies of the planar `ExternalAssumptions`, `ConditionalVanishing`,
  and `Conclusion` modules, moved into the `HodgeConjecture.Planar`
  namespace so they can evolve independently here;
- a planar Chow-projector layer built on those local copies:
  branch purity, finite-étale rigidity, and no hidden inertia force the
  planar off-diagonal collision idempotent to vanish, while that idempotent
  independently realizes as a bigraded Chow/cohomological projector.

The formalized implication chain is therefore:

\[
\text{vanishing collision defects}
\Longrightarrow
\text{product ring and affine-scheme decomposition}
\Longrightarrow
\text{Chow-class and cohomological projector},
\]

with boundary inertia controlling codimension-one extension and the
compactification/purity interface converting those local extensions into a
global selector.

There are two deliberately distinct purity layers.  The imported
`BranchPurityA2` statement says that absence of codimension-one ramification
forces the finite normalization to be étale.  The local interface
`CompactificationSelectorExtension` says that extension of a selector at all
height-one boundary components forces a global idempotent extension.  The
locally copied planar modules preserve the first layer without changing the
source files in `collision-ideals`.  The module
[`Planar/ChowProjector`](HodgeConjecture/Planar/ChowProjector.lean) connects it
to the Chow/Hodge realization machinery without conflating it with the second.
Its explicit-hypothesis theorem is accompanied by a wrapper using the copied
standard-geometry assumptions, so `#print axioms` continues to expose the
unformalized geometric input.

The copied foundational modules live under
[`HodgeConjecture/Foundations`](HodgeConjecture/Foundations).  Their imports
have been redirected to one another, and the Hodge-native collision and
inertia modules now consume these local copies.  The original
`collision-ideals` worktree remains unchanged; its pinned dependency is kept
for the planar normalization/Keller compatibility layer that has not yet been
generalized away from polynomial maps.

The remaining work is to instantiate the explicit geometric interfaces.  For
a concrete compactification one must supply:

1. the local comparison between the collision Noether different and the
   valuation-theoretic different;
2. the realization of ramification by relative inertia in a Galois closure;
3. the purity theorem identifying global selector extensions with extension
   across every height-one boundary component;
4. the actual proper correspondence-cycle ring, its rational-equivalence
   ideal, and the selector cycle class;
5. the action of those cycles on the desired motivic or Hodge realization and
   the proof that rational equivalence acts trivially.

Mathlib does not yet provide a general Chow-correspondence or Hodge-structure
library.  The project therefore isolates those later constructions behind
explicit interfaces instead of treating them as already available.
