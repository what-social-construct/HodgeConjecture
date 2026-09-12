# Zero-cycles and rational equivalence on actual finite split schemes

Status: CYCLE MODULE, EMPTY PRINCIPAL-DIVISOR INDEX, CHOW COORDINATES,
AND RATIONAL SCALAR EXTENSION BUILT AND VERIFIED.

Date: 2026-09-11. This advances
[0010-split-integral-subschemes.md](0010-split-integral-subschemes.md).
Canonical manuscript: `paper/main.tex`, producing the single `paper/main.pdf`.

Progress: the product, multiplicity, and geometric composition step below
is implemented in [0012-split-chow-composition.md](0012-split-chow-composition.md).
The original checkpoint and its verification record are retained here.

## Objects and theorem

Fix a field `k`, a finite label type `I`, and `Z_I = Spec(k^I)`. The
preceding geometric classification gives actual integral ideal-sheaf
subschemes `IntSub(Z_I)` and an equivalence `I ≃ IntSub(Z_I)`. Every member
has dimension zero.

The new cycle module is defined on these actual generators:

```text
Z_0(Z_I;R) := IntSub(Z_I) →₀ R,
pointCycle i := the fundamental cycle of the point subscheme s_i.
```

The construction works for general coefficient semirings at the cycle
stage and commutative rings at the rational-equivalence stage. The
manuscript uses `R = ℤ` and `R = ℚ`. The generator equivalence constructs
the linear point-coordinate equivalence

```text
coordinates : Z_0(Z_I;R) ≃ₗ[R] (I → R),
coordinates z i = z(pointIntegralSubscheme k I i).
```

The source of principal-divisor data is built from the actual geometry:

```text
IntegralCurve := {W : IntSub(Z_I) // dim W = 1},
PrincipalDivisorData := Σ W : IntegralCurve, Units(functionField W).
```

The dimension-zero theorem proves both indexing types empty. Consequently
there is a unique ambient principal-divisor assignment from this empty
domain to the cycle module, with intended value `(ι_W)_* div_W(f)`.
Define its generated relation submodule and quotient:

```text
Rat_0(Z_I;R) := span_R(range principalDivisor),
z ∼rat w    := z - w ∈ Rat_0(Z_I;R),
CH_0(Z_I;R) := Z_0(Z_I;R) / Rat_0(Z_I;R).
```

Emptiness, not a supplied vanishing hypothesis, then proves

```text
Rat_0(Z_I;R) = 0,
(z ∼rat w) ↔ z = w,
CH_0(Z_I;R) ≃ₗ[R] Z_0(Z_I;R) ≃ₗ[R] (I → R).
```

The actual cycle module, its relation submodule, and its quotient are
separate definitions. Coordinates are constructed after the cycle module;
they are not its definition.

## Exact source matching

- [Stacks, Definition 42.8.1, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
  defines cycles using integral closed subschemes and locally finite
  support. Here every integral subscheme has dimension zero, and the
  generator type is finite, so `Finsupp` records precisely these sums.
- The field-base setup is
  [Example 42.7.2, Tag 02QM](https://stacks.math.columbia.edu/tag/02QM).
  [Lemma 42.7.5, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
  identifies the source's cycle dimension with ordinary dimension over
  this base. The ambient split scheme is finite, hence finite type.
- [Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
  indexes rational-equivalence generators by integral closed subschemes of
  one higher dimension and nonzero rational functions. For zero-cycles
  here, the corresponding actual curve type is empty. The use of units in
  the actual scheme function field matches the nonzero-function input.
  Both finite sums and locally finite families therefore reduce to the
  empty family, whose cycle is zero.

These citations specify the conventional cycle and rational-equivalence
objects. Lean proves the specialized geometric emptiness and quotient
calculation directly. The principal-divisor map is the unique map from the
proved-empty geometric type; a general divisor algorithm is not part of
this construction.

## Integral and rational coefficients

`rationalize` is the coefficient-extension map from integral to rational
cycles. It is `ℤ`-linear, injective, sends each fundamental point cycle to
the same point cycle, and agrees with integer-to-rational casting in point
coordinates.

The scalar-extension theorem constructs

```text
rationalizationEquiv : (ℚ ⊗[ℤ] Z_0(Z_I;ℤ)) ≃ₗ[ℚ] Z_0(Z_I;ℚ),
q ⊗ z ↦ q • rationalize z.
```

This follows from finite point coordinates and the tensor-product
equivalence for finite function modules. The quotient-by-zero equivalences
then produce the canonical Chow scalar extension:

```text
chowRationalize : CH_0(Z_I;ℤ) →ₗ[ℤ] CH_0(Z_I;ℚ),
chowRationalizationEquiv :
  (ℚ ⊗[ℤ] CH_0(Z_I;ℤ)) ≃ₗ[ℚ] CH_0(Z_I;ℚ),
q ⊗ [s_i] ↦ q • [s_i].
```

The first map is injective and commutes with the cycle quotient maps. The
second identifies the rational-coefficient quotient with the usual rational
scalar extension of the integral Chow group.

## Lean and manuscript parity

Paths are relative to `HodgeConjecture/`.

| Module | Main declarations |
| --- | --- |
| `Realization/Chow/Examples/SplitZeroCycles.lean` | `Cycles`, `pointCycle`, `coordinates`, `coordinates_apply`, `coordinates_pointCycle`, `rationalize`, `rationalize_injective`, `coordinates_rationalize` |
| `Realization/Chow/Examples/SplitZeroCycleBaseChange.lean` | `rationalizationEquiv`, `rationalizationEquiv_tmul`, `rationalizationEquiv_tmul_pointCycle` |
| `Realization/Chow/Examples/SplitRationalEquivalence.lean` | `IntegralCurve`, `PrincipalDivisorData`, `principalDivisor`, `principalDivisor_unique`, `relations`, `relations_eq_bot`, `RationallyEquivalent`, `rationallyEquivalent_iff_eq`, `Chow`, `classMap`, `classMap_bijective`, `chowEquivCycles`, `chowCoordinates`, `chowCoordinates_pointCycle` |
| Same rational-equivalence module | `chowRationalize`, `chowRationalize_classMap`, `chowRationalize_injective`, `chowRationalizationEquiv`, `chowRationalizationEquiv_tmul`, `chowRationalizationEquiv_tmul_classMap`, `chowRationalizationEquiv_tmul_pointCycle` |

All these declarations lie in `SplitZeroCycles`. Claim A11i and parity
item SP21 record the same additive Chow construction. Canonical notation is
`Z_0(Z_I;R)`, `Rat_0(Z_I;R)`, and `CH_0(Z_I;R)`. The existing matrix
coefficient module retains its own earlier definition.

## Next construction

Identify the actual product `Z_I ×_k Z_I` with its point-pair integral
subschemes. Construct the geometric pullback and pushforward operations on
these zero-cycles and prove that correspondence composition is the matrix
law, with rows indexing outputs and columns inputs. This will compare the
actual rational Chow correspondence algebra with the previously proved
additive split-span quotient `C_sp^add ≃ₐ[ℚ] M_I(ℚ)`.

The Betti and cycle-class action comparison follows that multiplicative
identification.

## Verification record

- The cycle, scalar-extension, and rational-equivalence modules compiled
  cleanly, including the Chow tensor comparison (2466 jobs for the
  rational-equivalence module build).
- `lake build` passed (2818 jobs). The only warnings are the two pre-existing
  `sorry` declarations in the unchanged root `Challenge.lean`.
- `lake env lean research/Verification.lean` passed. The new axiom reports
  contain only `propext`, `Classical.choice`, and `Quot.sound`. Checks include
  the empty scheme's zero Chow group and nonvanishing of actual point classes.
- The active `HodgeConjecture/` tree contains no `sorry`, `admit`, `axiom`,
  or `unsafe` declarations.
- Independent mathematical review confirmed the actual curve/function-field
  index, finite-support match, and zero-dimensional rational-equivalence
  specialization; source definitions and dimension conventions were verified.
- The canonical `paper/main.pdf` rebuilt successfully (21 pages), with no
  unresolved citations/references or overfull/underfull boxes. Pages 14--15,
  containing Theorem 7.5 and the tensor comparison, were visually checked.
- `git diff --check` passed; A11i, SP21, the gap map, and manuscript agree.
