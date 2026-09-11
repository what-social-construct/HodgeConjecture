# Legacy planar bridge snapshots

These files preserve the pre-self-contained planar bridge modules from
commit `0aa2ddc`.  They are retained for provenance and comparison with the
Jacobian-collision development, but they are not part of the current Lean
library: their imports refer to the former external `CollisionIdeals`
dependency.

The production development now owns its collision, normalization, inertia,
correspondence, and realization layers under `HodgeConjecture/`.  Any useful
argument from these snapshots should be ported theorem-by-theorem into those
local namespaces with all geometric inputs kept explicit.

The original production paths were:

- `HodgeConjecture/Planar/ChowProjector.lean`;
- `HodgeConjecture/Planar/Conclusion.lean`;
- `HodgeConjecture/Planar/ConditionalVanishing.lean`;
- `HodgeConjecture/Planar/ExternalAssumptions.lean`.
