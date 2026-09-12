# Actual integral closed subschemes of finite split schemes

Checkpoint update: the cycle module on these actual integral subschemes and
its rational-equivalence quotient are now constructed in
[0011-split-zero-cycles.md](0011-split-zero-cycles.md). The no-curves theorem
proves that the principal-divisor indexing type is empty. The historical
proof and verification record below is preserved.

Status: ACTUAL INTEGRAL CLOSED SUBSCHEMES CLASSIFIED; DIMENSION-ZERO
AND NO-CURVES THEOREMS PROVED.

Date: 2026-09-11. This advances
[0009-split-span-additive-quotient.md](0009-split-span-additive-quotient.md).
Canonical manuscript: `paper/main.tex`, producing the single `paper/main.pdf`.

## Exact geometric statement

Let `k` be any field, `I` any finite label type, and `Z_I = Spec(k^I)`.
For every actual closed immersion `f : X → Z_I` with `X` integral, there
is a unique label `i : I` for which an isomorphism

```text
e : X ≅ Spec k,        e.hom ≫ pointInclusion k I i = f
```

exists. Thus the classification respects the given embedding as a scheme
morphism, rather than identifying only its underlying point. Uniqueness
in `existsUnique_pointIso_of_isIntegral` quantifies over the label `i`.

The canonical object `IntegralClosedSubscheme k I` is the subtype

```text
{J : (Spec(k^I)).IdealSheafData // IsIntegral J.subscheme}.
```

It records actual ideal-sheaf data and their associated closed subschemes.
`pointIdealSheaf k I i` is the kernel ideal sheaf of the labelled point
inclusion. The construction proves it defines an integral subscheme and
gives the equivalence

```text
labelEquivIntegralClosedSubscheme : I ≃ IntegralClosedSubscheme k I.
```

The canonical subscheme type has a `Finite` instance, and
`integralClosedSubscheme_dimension` proves each of its members has
topological Krull dimension zero.

In the manuscript, the latter set is denoted `IntSub(Z_I)`; the point ideal
sheaf is `I(s_i)`. Labels and point presentations use the existing `s_i`
notation, without adding another cycle type at this step.

## Actual dimension bound

The underlying topology of `Z_I` is discrete. Its irreducible subsets are
exactly the singleton labelled points. Lean therefore proves

```text
dim Z_I ≤ 0,
dim X ≤ 0       for every actual closed immersion X → Z_I,
dim X = 0       for every nonempty such X,
¬ 1 ≤ dim X     for every such X.
```

Here `dim` is Mathlib's `topologicalKrullDim`, defined from chains of
irreducible closed subsets. The at-most-zero statement also covers the
empty scheme. In particular, no integral one-dimensional closed subscheme
exists.

## Proof spine

1. Discreteness identifies every irreducible subset with a labelled point.
   The image of an irreducible scheme under a scheme morphism is therefore
   one point.
2. For the integral closed immersion `f`, lift through the corresponding
   open point component `s_i : Spec k → Z_I`. The lift is itself a closed
   immersion, and nonemptiness of the integral source makes it surjective.
   A surjective closed immersion into the reduced scheme `Spec k` is an
   isomorphism. Its composite with `s_i` is the original `f`.
3. Apply this classification to each canonical ideal-sheaf subscheme.
   Taking the kernel of its inclusion identifies its ideal sheaf with the
   point ideal sheaf. Supports distinguish distinct labels, giving the
   equivalence with `I`.
4. Singleton irreducible closed subsets have no strict nontrivial chains;
   dimension is at most zero and cannot increase under a closed embedding.
   Nonemptiness supplies the opposite inequality for the equality case.

This is the active geometric proof branch. It uses the existing scheme
isomorphism, open-immersion, closed-immersion, and ideal-sheaf APIs.

## Verified commutative-algebra companion

The independent supporting module `CommutativeAlgebra/SplitFieldQuotient.lean`
proves that every prime ideal `p` of `k^I` is the kernel of evaluation at a
unique coordinate:

```text
∃! i, p = ker(ev_i),
evalQuotientEquiv : (k^I / ker(ev_i)) ≃ₐ[k] k.
```

The equivalence sends the class of a coefficient function to its value at
`i`. It follows that every prime quotient is isomorphic to `k` as a
`k`-algebra. The argument uses the prime-spectrum decomposition of a finite
product and the quotient-kernel equivalence for surjective evaluation.

This module is a directly verified companion, not a second dependency of
the active geometric proof or an additional hypothesis. It is explicitly
imported by the verification script; the actual scheme classification and
dimension modules are exported through the correspondence umbrella.

## Lean and manuscript parity

Paths are relative to `HodgeConjecture/`.

| Module | Main declarations |
| --- | --- |
| `Correspondence/Examples/SplitPointDimension.lean` | `discreteTopology`, `isIrreducible_iff_point`, `range_eq_point`, `topologicalKrullDim_le_zero_of_isClosedImmersion`, `topologicalKrullDim_eq_zero_of_isClosedImmersion`, `not_one_le_topologicalKrullDim_of_isClosedImmersion` |
| `Correspondence/Examples/SplitIntegralSubschemes.lean` | `existsUnique_pointIso_of_isIntegral`, `IntegralClosedSubscheme`, `pointIdealSheaf`, `pointIntegralSubscheme`, `labelEquivIntegralClosedSubscheme`, `integralClosedSubscheme_dimension` |
| `CommutativeAlgebra/SplitFieldQuotient.lean` | `existsUnique_prime_eq_ker_eval`, `evalQuotientEquiv`, `evalQuotientEquiv_apply_mk`, `exists_prime_quotient_equiv` |

The manuscript's “Integral closed subschemes of split points” theorem
records the classification and dimension statement after the exact
additive presentation. Claim A11h and parity item SP20 record the same
objects and arrows.

## Next construction

Form the zero-cycle group on the actual integral closed subschemes just
classified, with rational coefficients as needed. Define its
rational-equivalence relations and use the no-curves theorem to show that
there are no one-dimensional integral closed subschemes contributing
generators in this setting. This specializes
[Stacks, Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
to the proved actual geometry.

Next compare the resulting cycle quotient and its geometric correspondence
composition with `C_sp^add ≃ₐ[Q] M_I(Q)`, preserving the rows-as-outputs,
columns-as-inputs convention. The corresponding Betti cycle-class and
action comparisons are subsequent steps.

## Verification record

- Independent mathematical audit of the classification and dimension
  statements passed.
- `lake build` passed: 2813 jobs. The only warnings are the two pre-existing
  `sorry` declarations in unchanged `Challenge.lean` (declarations at
  lines 33 and 46).
- `lake build HodgeConjecture HodgeConjecture.CommutativeAlgebra.SplitFieldQuotient`
  also passed, including the directly imported algebra companion.
- `lake env lean research/Verification.lean` passed. It checks the empty
  ambient case and the emptiness of the actual integral-curve indexing type.
- Axiom checks for the scheme classification, ideal-sheaf equivalence,
  no-curves theorem, and prime-quotient equivalence report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The active source scan finds no `sorry`, `admit`, `axiom`, or `unsafe`
  declarations in `HodgeConjecture/`.
- The canonical PDF rebuilt successfully: 20 pages. The final LaTeX log
  has no warnings, undefined references, or overfull/underfull boxes.
- `git diff --check` passed.
