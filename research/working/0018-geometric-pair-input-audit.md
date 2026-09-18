# Geometric input audit and regular-pair controls

Date: 2026-09-18. Checkpoint: SP69. This is a research audit, not a new
manuscript theorem or a completed Hodge construction. The production
regular-pair criterion from SP68 is unchanged.

## 1. What the current cover package supplies

`HodgeConjecture/Boundary/Normalization/InertiaDiagram.lean` defines
`NormalizedCover` using a marked finite normal closure, finite intermediate
and normal-closure normalization models, and an open immersion of the
visible scheme. It does not require that open immersion to be surjective
or that the normalization be unramified along the deleted locus.

The active library audit found consumers of a supplied `NormalizedCover`,
but no construction of one from a specific smooth projective variety and
cover. The split Chow/Betti examples are actual constructions in a separate
part of the library; they do not instantiate this normalization package.
Consequently, there is not yet application-specific boundary geometry
from which the regular pairs can be extracted.

The existing theorems provide two useful ingredients, not the missing pair:

- `fixedLocusIdeal_ne_bot` supplies a nonzero element of the fixed ideal.
- `intermediateFixingSubgroup_normalCore_eq_bot`, over a perfect base
  field, makes the action on conjugate sheets faithful.

Neither ensures that a moving-boundary element acts injectively modulo a
chosen fixed element. Choosing that first element arbitrarily is itself
unsafe for this purpose, as the formal controls below show.

## 2. A deleted ramification divisor survives all the weak inputs

This is an explicit mathematical model, not a Lean construction of a
`NormalizedCover` in this checkpoint. Let `k` have characteristic zero and
take

\[
 B=k[x],\quad K=k(x),\quad L=N=k(t),\quad x=t^2,\quad T=k[t].
\]

The finite normal extension has involution `t -> -t`. Its normalization is
`T`: this ring is finite over `B`, integrally closed, and has fraction field
`N`. Mark the open `U=D(t)` in `Spec T`.

The visible map is étale: its presentation is
`B[t,1/t]/(t^2-x)`, with derivative `2t` invertible. This uses the
[standard étale definition, Stacks 00UB](https://stacks.math.columbia.edu/tag/00UB)
and [standard étale implies étale, Stacks 00UC](https://stacks.math.columbia.edu/tag/00UC).
It is finite étale over `D(x)`, not a finite cover of all of `Spec B`.

For the nontrivial subgroup `I`, every difference `h(-t)-h(t)` is divisible
by `t`, and the difference for `h=t` is `-2t`. Hence `J_fix(I)=(t)`.
The deleted set `V(t)` is invariant under the involution; both moved sheets
have boundary ideal `(t)`. Therefore

\[
 J_{\mathrm{fix}}(I)=J_{\mathrm{mov}}(I)
   =J_{\mathrm{fm}}(I)=(t).
\]

The height-one prime `(t)` contains this ideal. Thus separation fails,
and the already proved SP67 pole theorem obstructs uniform trace landing.
No regular pair in this combined ideal can satisfy the SP68 criterion.
For `k=C`, the same local model is the affine chart of the squaring map
`P^1 -> P^1`, whose restriction to `G_m` is étale. A smooth projective
ambient variety does not, by itself, remove this boundary issue.

This is a counterexample to an implication from the *current weak cover
inputs*, not a counterexample to the Hodge conjecture or to SP68.

## 3. Formal algebra controls: the choice of first element matters

`research/RegularPairGeometryControls.lean` is a standalone research file,
outside the production imports and centralized production declaration
inventory. Its checks use the existing quotient and ideal
carriers, not a new geometric-input package.

In the nested polynomial ring `Q[y][x]`, put `A=(x)` and `M=(y)`.
The choice `f=x`, `g=y` works: modulo `x` the ring is `Q[y]`, where
multiplication by `y` is injective. The existing generic SP68 theorem
then excludes height-one primes containing `A+M`. A separate check proves
`A+M` is proper, so this is not a unit-ideal example.

But `f=xy` is also a nonzero element of `A`. For this first element,
**no** `g in M` is regular modulo `f`: the nonzero residue class of `x`
is annihilated by every multiple of `y`. Thus nonzero fixed-element
existence cannot be combined with an arbitrary subsequent choice of a
moving element.

The general algebraic obstruction is: in a domain, if `a != 0` and `b`
is not a unit, then every `g in (b)` is a zero divisor on `T/(ab)`.
Indeed `g*a in (ab)`, while `a in (ab)` would force `b` to be a unit by
cancellation. These are algebraic controls; `A` and `M` have not been
identified with the actual fixed and moving ideals of a constructed cover.

Validation: `lake env lean research/RegularPairGeometryControls.lean`
passes without warnings. All eight named diagnostic theorems pass the
enforced axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`).
`lake build` also passes (3161 jobs), with only the pre-existing expected
`Challenge.lean` placeholder warnings. The production declaration
inventory, manuscript, and PDF are unchanged; the inventory audit and PDF
build were not rerun for this research checkpoint. No production theorem
or global hypothesis changes are required by this audit.

## 4. Exact obstruction for a specified first element

For a Noetherian ring `T`, a specified `f`, and an ideal `M`, the
mathematical existence test is

\[
 \exists g\in M\text{ regular on }T/(f)
 \quad\Longleftrightarrow\quad
 \forall\mathfrak p\in\operatorname{Ass}_T(T/(f)),\quad
 M\nsubseteq\mathfrak p.
\]

This follows from finiteness of associated primes for the finite module
`T/(f)`, the description of zero divisors as their union
([Stacks 10.63.5 and 10.63.9](https://stacks.math.columbia.edu/tag/00L9)),
and [finite prime avoidance, Stacks 00DS](https://stacks.math.columbia.edu/tag/00DS).
The zero quotient is allowed; then regularity is vacuous.

The pinned Mathlib has `associatedPrimes.finite`,
`biUnion_associatedPrimes_eq_compl_regular`, and
`Ideal.subset_union_prime_finite`. This is an available reduction, not a
newly formalized existence theorem or a proof of geometric avoidance.
For the boundary route, the missing content is how the actual moving
ideal avoids these primes for a suitably chosen actual fixed element.

## 5. Choose the geometric construction before adding more criteria

Two different next constructions remain possible:

1. **Finite étale cover over the whole smooth projective base.** Build
   its affine normalization data with the entire intermediate model
   visible. In the full-visible situation every conjugate boundary ideal
   is the unit ideal. Core-freeness makes a nontrivial subgroup move some
   sheet, so `J_mov(I)=T`; a nonzero fixed element and `g=1` give a pair.
   This is a mathematical positive subclass, not yet implemented here.
   The class-generation problem under the Chow--Betti map remains separate.
2. **A genuinely nonempty boundary compactification.** Specify the actual
   cover and compactification, compute their fixed and moving ideals, and
   identify an independent condition excluding the ramified-divisor model
   above. Étaleness on the visible open, normality, and finite denominator
   clearing alone cannot supply that condition.

Neither choice changes the main smooth-projective Hodge target. The
full-visible condition must not be silently added to the general route.
The next design choice has been requested from the user. Until that choice
is settled, do not replace the construction with another assumed regular
pair, associated-prime avoidance assertion, or uniform landing package.
