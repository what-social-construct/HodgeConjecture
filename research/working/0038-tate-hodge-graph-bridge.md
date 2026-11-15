# Proved Hodge compatibility for the existing Tate graph bridge

Date: 2026-11-08.

This completes the Hodge-compatibility step in the existing
[target-first checklist](../TARGET_BRIDGE.md). It supplies a previously
explicit input of the original equivalence theorem; general geometric
comparison, Chow construction/detection and coverage retain their scope.

## Actual Tate object and product

For a pure rational Hodge structure S of weight 2p on H, construct the
Tate line ℚ(-p) with F^k equal to its whole genuine complexification when
k ≤ p, and zero otherwise. Finite dimension, boundedness and opposedness
under canonical conjugation are proved. The sign convention is the one
already specified by `TateGraphProjector.lean`: type (p,p), weight 2p.

The existing rational product carrier ℚ × H has its actual tensor
complexification. Native `TensorProduct.prodRight` identifies it with
(ℂ ⊗_ℚ ℚ) × (ℂ ⊗_ℚ H). The product filtration is transported through
that canonical equivalence, which intertwines canonical conjugation.
Products of pure structures of the same weight are proved pure; hence
the Tate-plus-cohomology block is a genuine pure structure in this model.
No chosen basis or substitute complex vector space is introduced.

`PureRationalHodgeStructure.IsHodgeMorphism` means preservation of the
complex filtration after scalar extension of the original rational map.
`map_mem_piece` proves preservation of every recovered Hodge piece, using
the existing conjugation-naturality theorem.

## Compatibility theorem

For the unchanged rational graph operator

\[
 e_\alpha(t,x)=(t,t\alpha),
\]

the new theorem proves

\[
 e_\alpha\text{ is a Hodge morphism of }\mathbf Q(-p)\oplus H
 \quad\Longleftrightarrow\quad
 \alpha\in\operatorname{Hdg}^p(S).
\]

The independent rational Hodge space remains the inverse image of
F^p ∩ conjugate F^p under the original rational tensor embedding.
It is not defined by the graph predicate or the cycle-class image.

The proof first shows that a map from the Tate line is filtered exactly
when its value at 1 lies in F^p. Decreasingness supplies the lower
filtration levels; levels above p have zero Tate source. Rationality
supplies the conjugate-filtration condition. Native product coordinates
then identify graph preservation with preservation by that lower-left map.
The filtration argument needs only decreasingness, while the pure
specialization supplies its Hodge-theoretic interpretation.

## Existing equivalence, with one input discharged

[FilteredTateGraphProjector.lean](../../HodgeConjecture/Realization/Chow/FilteredTateGraphProjector.lean)
proves `classGraphHodgeCompatibility` for the existing filtration-derived
`cycleClassModel`. It invokes the original
`rationalHodgeConjectureAt_iff_everyClassGraphHodgeMorphismHasAlgebraicLift`
with that proved compatibility. Its public adapter is
`PureRationalHodgeStructure.rationalHodgeConjectureAt_iff_hodgeGraphLifts`.

The cycle map and its type proof, the correspondence action, the existing
`ClassGraphProjectorConstruction`, and the existing
`ClassGraphProjectorDetection` remain explicit. No new correspondence
algebra, encoding, detection map or equivalence interface was invented.
For geometric use, identifying S with the variety's pure cohomology and
constructing those Chow data remain necessary. Neither arbitrary-class
coverage nor a general Hodge-conjecture case follows from this adapter.

The actual P¹ model from the derived scheme filtration, bounded period
comparison and original ordinary Chow map instantiates this compatibility
in verification. Its rational graph maps preserve the actual recovered
Hodge pieces. No general P¹ Tate-motive correspondence algebra or
Chow construction/detection instance is asserted by that test.

## Ownership and validation

[TateHodgeStructure.lean](../../HodgeConjecture/Realization/TateHodgeStructure.lean)
owns canonical tensor-product subspaces, pure products and Tate lines,
the Hodge-morphism predicate and the original block-graph filtration
criterion. It imports no cycles, Chow, Betti/de Rham realization, boundary,
geometry or source-input package. The downstream Chow adapter uses the
old graph-projector equivalence; both public target and Chow umbrellas
export it. The semantic parity table records the same carriers and maps.

The new verification checks integer Tate indices, a wrong-cutoff control,
a rational class excluded by a proper filtration, preservation of Hodge
pieces and the actual geometric P¹ model. Its 23 axiom audits passed with
only `propext`, `Classical.choice` and `Quot.sound`. All import-boundary
checks passed. The full library build passed (5,108 jobs), as did local
documentation-link checks and `git diff --check`. A focused root-import
check verified all 16 new inventory exports. Existing unrelated
full-build warnings retain their previous scope.
