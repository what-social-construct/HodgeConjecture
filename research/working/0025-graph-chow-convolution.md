# Actual graph Chow convolution in the marked-Galois spine

Date: 2026-11-05. Main mathematical target first; no submission candidate,
publication or Jacobian submission is changed by this checkpoint.

## Recovered original spine

The original [canonical diagram](../archive/planning/0006-lean-spine-manuscript-outline.md)
and [target equivalence](../archive/planning/0003-hodge-target-equivalence.md)
describe the marked normal/Galois closure, the algebra of sheets `G/H`, and
the algebra decomposition `ℚ^(G/H) ≃ₐ[ℚ] ℚ × E_corner`. Selector multiplication
is diagonal in those coordinates. The constant-unit shear producing the
block operator is a separate linear equivalence. This algebraic
decomposition does not assert that every primitive Hodge class has an
algebraic representative.

The retained spine then needs a genuine Chow projector on the selected
geometric model, a residual map with its prescribed class/action square,
and Chow detection of the lower-left class. A raw closure only puts its
idempotence defect in the open-restriction kernel. Normal closure and
selector extension alone do not remove the Chow or realization obligations.
The historical planning documents remain provenance; the live claim and
gap ledgers control current theorem scope.

## Actual graph classes and geometric actions

`Correspondence/GraphChow.lean` derives homogeneity of each deck graph from
its actual integral graph-subscheme isomorphism. The degree is the existing
canonical field dimension of its source. The resulting graph classes and
weighted graph map land in the existing rational principal-relation
quotient. There is no supplied graph-degree or relation-descent hypothesis.

`GraphChowAction.lean` constructs actual pullbacks through the pair
isomorphisms `(x,z) ↦ (τx,z)` and `(x,z) ↦ (x,τ⁻¹z)`. Canonical grading
invariance and preservation of the original principal relations are proved.
Their Chow actions satisfy

```text
R_τ[Γ_σ] = [Γ_(στ)]       R_τ ∘ R_υ = R_(υτ)
L_τ[Γ_σ] = [Γ_(τσ)]       L_(στ) = L_σ ∘ L_τ.
```

Weighted linear extensions act on every Chow degree and retain their unit
and multiplication laws. Group-algebra idempotents induce idempotent
endomorphisms there.

## Convolution with exactly the actual Chow relations

`GraphChowAlgebra.lean` proves that the kernel of the actual graph-to-Chow
map is two-sided, using those geometric left/right pullbacks. Its quotient
is `GraphChowAlgebra`. The linear realization is injective into the existing
rational Chow group and has exactly the graph-generated image. Thus the
convolution algebra has precisely the equalities of those actual Chow
classes; it is not the free graph span with a new name.

Multiplication by a graph representative is characterized by the actual
Chow pullbacks on this image. Finite-group/subgroup averages give
idempotents, with their actual weighted graph-class formulas. The diagonal
minus an average is an orthogonal complementary idempotent; the sum realizes
the actual diagonal graph class.

No product on the whole ambient Chow group is constructed. Nor is the
exact graph kernel claimed to annihilate all ambient Chow degrees. No
nonvanishing follows from these hypotheses: in some geometries the
graph-generated Chow algebra can be zero.
Nor is a subgroup-average projector identified with the marked sheet
selector by this construction; that requires its own geometric action
comparison and the separate coordinate maps of the original spine.

## Relative to absolute products

`GraphChowBaseComparison.lean` proves that the existing closed pair inclusion
preserves the actual canonical field support degrees. Its genuine closed
Chow pushforward carries each relative graph to the same graph in the
absolute product over the field. The full weighted assembly square is
proved. The equal integer degrees are transported explicitly, preserving
the original absolute Chow quotient and its graph map.

The same square carries the exact relative graph kernel into the absolute
kernel. `graphChowBaseAlgHom` therefore gives multiplicative passage between
the two graph-generated Chow algebras. Its realization is precisely this
closed Chow pushforward after degree normalization, so actual graph
convolution idempotents remain idempotent in the absolute product.

The hypotheses retain integral source, separated cover, locally
finite-type source/pair field structures and Noetherian pair products. The
absolute comparison also requires a separated structural base and its
corresponding absolute-pair hypotheses. No new compactification existence
or open-restriction injectivity is assumed or proved.

## Remaining geometric step and review scope

Next select the existing normal-cover/compactification model and establish
its exact open graph comparison with these actual Chow maps. A prescribed
Betti action, class-dependent residual realization and coverage of the
independently specified Hodge classes remain open. Another generic Galois
closure or another coordinate decomposition does not supply them.

Automated submission review may compare every informal account with the
formal statements, including module docs and submission metadata. The main
README now explicitly names the two fixed-ring Challenge statements; they
are not the general Hodge target. Archives are labeled historical, but
archive/build exclusion does not itself exclude files from submission
review. This observation gives no evidence about why the separate Jacobian
review takes time. Submission cleanup and candidate selection remain deferred.

## Verification

`make check-graph-chow` builds the focused graph-Chow entry point and checks
the actual relations, action order, exact quotient, projector formulas and
relative-to-absolute square. An enforced import boundary excludes project
collision geometry and realization modules. Full integration and the
root-import theorem inventory are checked separately.

The focused build passes 3,274 dependency jobs; the standalone suite passes
18 regressions and 29 enforced axiom audits. These include finite subgroups
of arbitrary ambient groups and absolute passage of the average with its
actual Chow representative. The focused import closure has 151 project
modules and excludes all project realization and collision geometry.

The full default build passes 4,181 jobs. Root verification passes 1,297
declaration checks, 568 examples and 1,189 axiom reports. All reported
axioms lie in `propext`, `Classical.choice` and `Quot.sound`. The 392 library
modules plus the root pass the proof-token/external-Stacks-import scan.
All six import boundaries, pinned dependencies, local documentation links
and whitespace checks pass. The main README remains 69 lines. Job counts
include cached dependencies. Existing dependency style warnings and the
two intentional Challenge statement placeholders retain their prior scope;
the new source and standalone suite emit no warnings or proof placeholders.
