# Lean spine and unified manuscript outline

Status: IMPLEMENTED IN `paper/main.tex`; HUMAN REVIEW OPEN.

Opened: 2026-09-11.

This note replaces the historical Paper I/Paper II narrative with one
dependency-ordered proof account. The two old sources and their PDFs are
preserved under `research/archive/manuscripts/`. The sole active publication
source and PDF are `paper/main.tex` and `paper/main.pdf`; its sections
terminate at named Lean declarations. Archived drafts are not build targets.

## Editorial decision

Use one main paper.  The fixed-ring localization argument is a technical
appendix, not a separate logical predecessor of the projector construction.
The source audit is a short appendix.  Neither should determine the title,
abstract, or main-section order.

The manuscript must use three labels literally:

- **FORMAL**: proved from the displayed Lean parameters;
- **CONDITIONAL**: a Lean implication whose geometric input remains a
  parameter;
- **OPEN**: no construction of the required input is in the repository.

No abstract interface may be presented as a geometric instance, and no
conditional coverage theorem may be called a new case of the Hodge
conjecture.

## Canonical dependency spine

```text
abstract rational Hodge target
  HodgeClasses + TateGraphProjector
              ^
              | lower-left detection / exact graph action
              |
conditional marked realization ------------------------------- OPEN
  MarkedAugmentedRealization + GaloisMarkedRealization         theta,
              ^                                                action square,
              |                                                Chow model,
marked sheet graph normal form                                 coverage
  GenericProjector + MarkedAugmentedAlgebraDecomposition + MarkedBlockProjector
              ^
              |
generic selector / group projector extension
  GaloisSheets + InertiaSaturation + GaloisProjectorExtension
              ^
              |
codimension-one boundary separation
  InertiaDiagram + ConjugateNormalization + ConjugateBoundary
              ^
              |
normal closure and collision-to-sheet comparison
  Model + NormalClosure + SelectorComparison

collision geometry ---> finite-etale spans ---> group / Hecke projectors
  Collision/*          Correspondence/*        FiniteGroupProjector,
                                                GroupAlgebraProjector,
                                                HeckeProjector

compactification has two distinct branches:
  raw closure ---> defect in ker(r) --------------------------- OPEN vanishing
    ProjectorClosureDefect

  extended deck graphs + multiplicative comparison
       ---> compactified projector ---------------------------- CONDITIONAL
    CompactifiedGraphProjector
```

The arrows are not all implications in one linear theorem.  In particular:

- `NormalClosureData` already supplies normality and finiteness; over a
  perfect/characteristic-zero base its Galois structure, group, fixing
  subgroup, and canonical normalization deck action are derived, not repeated
  hypotheses;
- normality keeps conjugate embeddings in one `N` but does not make `G`
  abelian; deck maps lie over the base because they fix `K` and the induced
  `B`-scalars, while commutativity of the pointwise sheet algebra is an
  independent fact and does not extend to group/Chow convolution;
- collision component idempotents use pointwise ring multiplication;
- group and Hecke projectors use convolution;
- compactified projectors live in a supplied target algebra;
- Chow realization and the Hodge target need additional comparison data.

## Supporting localization branch

The following is a self-contained commutative-algebra branch and belongs in a
technical appendix:

```text
fixed-field normalization = fixed ring
  InvariantIntermediate
        |
prime inertia and selected fixed-ring map
  PrimeInertia + FixedRingUnramified
        |
height-one contraction and local DVR
  FixedRingLocalization
        |
centered valuation ring = normalization localization
  LocalizationBridge
        |
valuation inertia <= H  ==>  selected H-fixed localization unramified
  PrimeInertiaDescent
```

The final arrow still takes the fixed-inertia unramified theorem as an
explicit source input.  This branch does not construct the compactified Chow
correspondence or the residual realization map.

## Modules outside the active spine

These sources remain directly importable for provenance but are absent from
the root release path:

- `Boundary/Normalization/GlobalExtension.lean`: broad conditional
  normalization-purity/global-triviality prototype;
- `Realization/BoundaryProjector.lean`,
  `Realization/CohomologicalProjector.lean`, and
  `Realization/CompactificationProjector.lean`: historical commutative
  selector lane;
- `Realization/Chow/SelectorRealization.lean`: specialization of that lane.

They receive no section in the main proof narrative and no headline claim.

## Unified manuscript sections

### 1. Target before mechanism

State the fixed-model rational Hodge predicate and prove the equivalence with
lifting every canonical graph projector

```text
P_alpha(t,x) = (t,t alpha).
```

End at:

- `rationalHodgeConjectureAt_iff_everyHodgeClassHasGraphProjectorLift`;
- the separately parameterized Hodge-morphism version.

Say immediately that the repository supplies no concrete Chow/Hodge model.

### 2. Collision and finite-etale correspondence algebras

Develop the diagonal/off-diagonal collision decomposition, the admissible
finite-etale span algebra, graph composition, and the Galois collision sum.
Keep clopen selection and convolution idempotence visibly different.

End at:

- `finiteEtaleCollisionSchemeDecomposition`;
- `classOf_collision_eq_sum_graph`;
- `normalizedCollisionClass_isIdempotent` under its displayed model.

### 3. Group and Hecke projectors

Transport supplied idempotents from `Q[G]` and from the Hecke corner.  Treat
the subgroup average

```text
e_H = |H|^-1 sum_(h in H) [h]
```

as the structured generic convolution projector.  Do not identify it with a
pointwise sheet selector.

### 4. Marked sheets and the block normal form

Introduce the commutative pointwise algebra `A_H:=F_Q(H)=Q^(G/H)`, its
multiplicative augmentation `ev_H`, the base selector `q_H`, the augmentation
ideal `E_H=ker(ev_H)=(1-q_H)`, and `a_H=q_H-1`.  Record the regular source
action as an algebra homomorphism.  Give the residual corner the internal unit
`1-q_H` and prove the genuine algebra equivalence
`A_H ≃ₐ[Q] Q × E_H^corner`, with `q_H ↦ (1,0)` and
`1-q_H ↦ (0,1)`.  Separately prove that multiplication by `q_H` is
diagonal after forgetting to the underlying selector coordinates and is
`P_(a_H)` in the constant-unit linear splitting, with the explicit linear
shear relating them.

Use `U=Q×Q`, the universal algebra of one idempotent, as the active common
multiplicative source.  The marked selector, compactified correspondence, and
target graph projector each induce an honest algebra homomorphism out of `U`.
State restriction and realization compatibility as equalities of composites,
and package the action square as a morphism of `U`-representations.  Keep the
residual realization `theta:E_H -> V` visibly rational linear.  A
multiplicative map from the whole `F_Q(H)` into a generic correspondence
algebra is an optional stronger interface.  Do not place a map
`A_H -> Q[G]` in the active spine; `SheetLinearization.lean` is auxiliary and
direct-import-only.

End at `LinearAlgebra.MarkedAugmentedAlgebraDecomposition` for the algebra
equivalence and the shared `LinearAlgebra.BlockGraphProjector` lemmas for the
linear shear calculation, followed by their marked-sheet specializations.

### 5. Normalization and codimension-one separation

Construct the canonical conjugate legs, pull every visible boundary to the
common normal-closure normalization, and state the fixed--moving separation
condition.  With the displayed center comparison, ramification-index
comparison, and formal unramifiedness input, derive exactly

```text
Ram^(1)(Y_N/B) = empty.
```

Stop there.  The section must not infer global etaleness, triviality of the
normal closure, or vanishing of a Chow-convolution defect.

Before the boundary argument, display the multiplicative normal-closure
augmentation square.  Its top arrow is
`normalClosureTensorToGenericSheets : N ⊗[K] L →ₐ[N] N^(G/H)`;
base-sheet evaluation after this arrow equals
`normalClosureTensorDiagonal`.  Under perfectness the top arrow is an algebra
equivalence.  This is the honest field-to-sheet bridge and introduces no
sheet-to-group-algebra map.

### 6. The compactification fork

Present both honest formal endpoints.

1. A raw closure `Pi` of `pi_H^eta` has
   `Def(Pi)=Pi^2-Pi` in `ker(r)`.  Boundary support and vanishing are open.
2. If compactified deck graphs and the multiplicative restriction square are
   supplied, the group-algebra idempotent maps to a compactified idempotent.
   This is conditional but its defect vanishes by formal multiplicativity.

This section is the correct location for the boundary-defect discussion.

### 7. Conditional realization and the exact gap

Use the canonical maps from `U` attached to the generic selector and its
compactified extension.  Prove the restriction composite square, then use a
linear residual map `theta:E_H -> V` and the representation-morphism action
square to identify the lower-left class.  Surjectivity of `theta` upgrades
that equality to the whole graph operator and to `palomarTargetSquare`, an
equality of algebra-homomorphism composites.  Class-dependent coverage
implies the modeled Hodge target; the reverse direction uses a separately
named strong replacement hypothesis.  Treat a full sheet-algebra
presentation as an optional stronger variant, not a prerequisite.

Conclude with the actual missing morphism package:

```text
theta_alpha : E_(H_alpha)(-p) --> h(X),
```

together with a compactified correspondence, its action square, a genuine
Tate-augmented Chow model, and classwise coverage.  Constructing `theta_alpha`
from an already algebraic representative of `alpha` is circular.

### Appendix A. Height-one fixed-ring descent

Give the supporting localization chain above in theorem/proof form.  Its role
is to compare valuation and prime inertia at one selected branch.

### Appendix B. Lean declaration map and assumptions

One table only: manuscript result, Lean declaration, module, and status.
List external mathematical inputs compactly, at the exact theorem that takes
them as parameters.  Do not organize the paper around source tags.

## Section parity gate

For every theorem-like paragraph in the canonical manuscript:

1. identify its terminal Lean declaration;
2. copy the Lean quantifier order into the prose;
3. name every non-instance proposition parameter;
4. assign exactly one of FORMAL, CONDITIONAL, OPEN;
5. use the notation registry in `0005-semantic-parity-cleanup.md`;
6. exclude historical compatibility wrappers from the statement map.

Only after this gate and the build/source checks pass should `paper/main.tex`
be copied to `research/queue/`.
