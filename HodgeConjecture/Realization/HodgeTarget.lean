module

public import HodgeConjecture.Realization.Chow.FilteredTateGraphProjector
public import HodgeConjecture.Realization.HodgeClasses
public import HodgeConjecture.Realization.FilteredHodgeTarget
public import HodgeConjecture.Realization.HodgeTransport

@[expose] public section

/-!
# Rational Hodge target and projector reformulation

This umbrella module collects the abstract fixed-variety
cycle-class-surjectivity schema for the rational Hodge conjecture, its
family-indexed form, and its canonical Tate-block graph-projector
reformulation.

It also exports the filtration-derived rational target and the adapter
from a pure rational Hodge structure. This target is independent of the
cycle map; general geometric comparison and purity remain separate inputs.

The equivalence requires explicit Chow-level graph construction and
lower-left-block detection data. For a pure rational Hodge structure the
graph/Hodge compatibility is now proved using the actual Tate-product
filtration, and supplies the existing Hodge-morphism equivalence. The
current finite-cover realization does not yet
instantiate those data or prove that it produces every Hodge-class graph
projector.
-/
