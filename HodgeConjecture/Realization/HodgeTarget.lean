module

public import HodgeConjecture.Realization.Chow.TateGraphProjector
public import HodgeConjecture.Realization.HodgeClasses

@[expose] public section

/-!
# Rational Hodge target and projector reformulation

This umbrella module collects the abstract fixed-variety
cycle-class-surjectivity schema for the rational Hodge conjecture, its
family-indexed form, and its canonical Tate-block graph-projector
reformulation.

The equivalence requires explicit Chow-level graph construction and
lower-left-block detection data.  A formulation in terms of morphisms of
Hodge structures additionally requires the explicit graph/Hodge
compatibility interface.  The current finite-cover realization does not yet
instantiate those data or prove that it produces every Hodge-class graph
projector.
-/
