# Actual degree-zero Betti cycle classes and correspondence action

Status: PROVED; FULL BUILD, DECLARATION/AXIOM VERIFICATION,
AND SINGLE-PDF CHECKS PASS.

Date: 2026-09-11. This advances
[0012-split-chow-composition.md](0012-split-chow-composition.md).
Canonical manuscript: `paper/main.tex`, producing the single `paper/main.pdf`.

Advancement: the independent finite Hodge data and actual geometric
Tate-block construction/detection are implemented in
[0014-split-hodge-tate-block.md](0014-split-hodge-tate-block.md).
The verification record below remains the record of this Betti checkpoint.

## Checkpoint

The existing Chow groups are quotients of cycles on actual integral closed
subschemes of `Z_I = Spec(ℂ^I)`. Their geometric operations and correspondence
composition were constructed before identifying their point coordinates
with matrices. This step constructs the topological target independently:

```text
actual complex-algebra points, with evaluation-induced topology
→ actual continuous singular simplices and the two-face coboundary
→ degree-zero singular cohomology
← normalized cycle classes from actual rational Chow groups.
```

The cycle-class map is a linear equivalence. It respects geometric
pushforward/finite transfer, flat pullback, and intersection/cup product.
The cohomological pull--cup--transfer action intertwines the geometric
Chow action and gives a rational algebra representation of actual Chow
endomorphisms.

## Actual complex points

Define `X_I = Z_I(ℂ) = Hom_ℂ-alg(ℂ^I, ℂ)`. These are actual algebra
homomorphisms, not copies of the finite labels by definition.

For each homomorphism, its prime kernel is a unique coordinate-evaluation
kernel. The algebra-map identity on constants then proves that the
homomorphism itself is evaluation at that coordinate. This constructs
`I ≃ X_I`, including the empty-label case.

The topology on `X_I` is induced by the injective map sending a
homomorphism to its function on the coordinate ring. The function space
uses pointwise convergence with ordinary complex topology. Thus every
regular-function evaluation is continuous and the point space is
Hausdorff. Its proved finiteness implies discreteness. This produces the
homeomorphism with discrete `I`, without defining the topology by transport
from labels.

Each algebra point gives an actual `Spec` morphism over `Spec ℂ`.
Precomposition by the actual coordinate-ring map induces the continuous
point map. Its scheme morphism commutes with the existing geometric map.
The product homeomorphism `X_(I×J) ≃ X_I × X_J` respects the two actual
projection maps.

## Singular degree zero

`Simplex X n` is the continuous-map space from Mathlib's standard
topological `n`-simplex to `X`. Its comparison with Mathlib's singular
simplicial set is explicit, including the face restrictions.

Zero- and one-cochains are unrestricted rational functions on these
actual simplices. The coboundary is

```text
(δ⁰ φ)(σ) = φ(σ restricted to terminal vertex)
           − φ(σ restricted to initial vertex).
```

Unreduced singular cochains begin at degree zero, so there is no incoming
boundary in that degree. The module `H0 X` is literally the kernel of this
coboundary, with its subalgebra structure proved from the cocycle
equations. It is not a coefficient module renamed cohomology.

For a discrete space, connectedness of the standard one-simplex forces
its continuous maps to be constant. The two faces agree, the coboundary
vanishes, and evaluation on point zero-simplices gives
`H0 X ≃ₐ[ℚ] (X → ℚ)`. Specializing to the constructed complex-point
space gives `H_B^0(X_I;ℚ) ≃ₗ[ℚ] (I → ℚ)`.

Pullback precomposes actual singular simplices with an actual continuous
map. Cup product is multiplication of zero-cochains, with preservation of
the cocycle condition proved. Transfer is defined on actual point fibers,
before passing to finite label coordinates, and satisfies the degree-zero
projection formula.
The actual lifts of a continuous zero-simplex are separately classified
by its actual point fiber. `transfer_simplex_eq_sum_lifts` proves that
the constructed transfer is exactly summation over these singular-simplex
lifts, making the conventional transfer normalization explicit in Lean.

## Cycle class and action

The point basis on actual Chow and the evaluated singular-cocycle basis
construct

```text
cl_I : CH_0(Z_I;ℚ) ≃ₗ[ℚ] H_B^0(X_I;ℚ),
cl_I([s_i]) = δ_i,
```

where `δ_i` is the characteristic cocycle of the actual point `ev_i`.
This is the usual complex-oriented, zero-dimensional cycle-class
normalization. The group and map are independent of any Hodge subspace.

For `f:S→I`, the actual operations satisfy

```text
cl_I(f_* z) = f_* cl_S(z),
cl_S(f^* w) = f^* cl_I(w),
cl_I(z · w) = cl_I(z) ∪ cl_I(w).
```

For an actual Chow correspondence `c` from `Z_I` to `Z_J`, define

```text
c_B,* u = p2_* (cl_(I×J)(c) ∪ p1^*u).
```

This is constructed from singular pullback, cup product, and actual-fiber
transfer. It is not defined by conjugating a matrix action through a
chosen coordinate equivalence. The comparison theorem proves

```text
cl_J(c_*z) = c_B,* cl_I(z),
(c_B,*u)_j = ∑ i, c_(i,j) u_i.
```

The action respects composition and the diagonal. Keeping this action
constructs the algebra homomorphism

```text
ρ_B,I : Γ_I^CH →ₐ[ℚ] End_ℚ(H_B^0(X_I;ℚ)).
```

Its unit and multiplicativity are consequences of the geometric
composition comparison, not a transferred definition of multiplication.

## Exact source matching

- [Hatcher, Algebraic Topology](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  §3.1 p.198, identifies ordinary degree-zero singular cohomology by the
  two-endpoint cocycle equation. We use actual singular simplices and
  their face maps. For our finite discrete spaces the resulting classes
  are precisely point functions. No arbitrary-space identification with
  locally constant functions is used.
- The same source, §3.2 p.206, gives the singular cup formula. Its
  degree-zero specialization is precisely the implemented product.
- The same source, §3.G p.321, defines finite-cover transfer using sums
  of simplex lifts. In this finite discrete specialization every simplex
  is constant, and its lifts are the points of the actual fiber. Use the
  construction componentwise: fiber cardinalities can differ and can be
  zero, so no globally fixed positive sheet count is assumed.
- [Deligne, The Hodge Conjecture](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf),
  §1 pp.1--2, defines cycle classes by complex-oriented Poincaré duality.
  A zero-dimensional complex component has positive point fundamental
  class; its dual is the characteristic cocycle. This compares the
  constructed normalized finite-point map with the conventional cycle
  class. No general Poincaré-duality or analytic Hodge theorem is imported
  into Lean as an axiom by this step.

The geometric operations on the other side retain the exact Stacks
source matches of `0012`. Their compatibility here is proved on the
independently constructed point and singular-cocycle bases.

## Lean and semantic parity

Paths below are relative to `HodgeConjecture/Realization/Betti/`.

| Module | Principal declarations |
| --- | --- |
| `Examples/SplitComplexPoints.lean` | `SplitComplexPoints.Point`, `evalPoint`, `existsUnique_eq_evalPoint`, `labelEquiv`, `pointTopology`, `isEmbedding_evaluation`, `pointDiscreteTopology`, `schemeMorphism`, `schemeMorphism_map`, `schemeMorphism_toBase`, `mapContinuous`, `productHomeomorph` |
| `SingularDegreeZero.lean` | `Simplex`, `simplexEquivSingularSet_face`, `coboundary`, `cocycles_toSubmodule`, `H0`, `eval`, `cup`, `face_eq_of_discrete`, `equivFunctions`, `pullback`, `pullback_comp` |
| `FiniteTransfer.lean` | `fiberSum`, `transfer`, `eval_transfer`, `transfer_projectionFormula` |
| `ZeroSimplexTransfer.lean` | `ZeroSimplexLift`, `zeroSimplexLiftEquiv`, `sum_zeroSimplexLifts`, `transfer_simplex_eq_sum_lifts` |
| `Examples/SplitCycleClass.lean` | `SplitBetti.Cohomology`, `coordinates`, `cycleClass`, `coordinates_cycleClass`, `cycleClass_pointCycle`, `pullback`, `pushforward`, `cycleClass_pullback`, `cycleClass_pushforward`, `cycleClass_intersection` |
| `Examples/SplitCorrespondenceAction.lean` | `action`, `cycleClass_action`, `coordinates_action`, `action_comp`, `diagonal_action`, `actionLinear`, `linearRepresentation`, `realization`, `realization_cycleClass`, `correspondenceAction` |

Claim A11k and semantic parity item SP23 record this checkpoint. The
notation registry keeps actual Chow, singular cohomology, and the point
coordinate module distinct, connected by the proved map `cl_I`.
Implementation coordinate adapters do not receive new realization symbols.

## Next construction and information retained

The next step at this checkpoint was the independently justified finite degree-zero Hodge
description, followed by the Tate-augmented block construction, actual
Chow lower-left detection, and their cycle-class comparison. Deligne's
decomposition in degree zero has only bidegree `(0,0)`, but this checkpoint
does not define the repository's Hodge subspace or instantiate its combined
Hodge model. Those objects and the geometric block comparisons are now
constructed in `0014`.

The cycle-class comparison here is an isomorphism: it loses no information
in the finite split degree-zero case. This does not reverse the earlier
loss from the free span algebra to its additive quotient. That loss remains
exactly the proved finite point-decomposition ideal.

## Verification record

- Each new module passes its direct build without warnings.
- `lake build` passes (3013 jobs). The only warnings are the unchanged
  `Challenge.lean` declarations at lines 33 and 46, which already use `sorry`.
- `lake env lean research/Verification.lean` passes. New regression checks
  cover absence of complex points of the empty scheme, zero cohomology of
  that scheme, the actual singular cocycle equation for point classes,
  empty and variable-cardinality transfer fibers, and the action of the
  point-pair correspondence from point 1 to point 0.
- The new point/topology, singular-face, cohomology, actual-simplex transfer,
  cycle-class, and action axiom reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`. No new axioms or admitted proofs
  were added.
- Independent mathematical and semantic reviews passed, including the
  point normalization, the actual evaluation topology, simplex-lift
  transfer, convolution/cup distinction, and correspondence variance.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` passes in
  `paper/`. The single PDF has 26 pages. The final log has no warnings,
  undefined references, or overfull/underfull boxes; Theorem 7.8 and its
  proof on page 17 were visually checked.
- Citation-key checks and `git diff --check` pass. A11k, SP23, the notation
  registry, gap/source ledgers, and the canonical manuscript agree.
