# Split marked-sheet residual realization and actual Chow action comparison

Status: PROVED; FULL BUILD, VERIFICATION, AND SINGLE-PDF CHECKS PASS.

Date: 2026-09-13. This advances
[0014-split-hodge-tate-block.md](0014-split-hodge-tate-block.md).
Canonical manuscript: `paper/main.tex`, producing the single `paper/main.pdf`.

## Checkpoint

The finite split Chow/Betti/Hodge model already has geometric graph encoding,
lower-left decoding, and the target equivalences. This checkpoint connects
its fixed correspondence action to actual marked finite-group sheet data.
The residual map is constructed from actual Chow point cycles before it is
composed with cycle class. The marked-coordinate change is an invertible
actual Chow correspondence, not a redefinition of the target action.

Let `G` be a finite group, `D≤G`, `S=G/D`, `s₀=D`, and
`I=S∖{s₀}`. Write `A_D=ℚ^S`, `q_D=1_{s₀}`,
`E_D=ker(ev_s₀)`, and `a_D=q_D−1`.

## Actual split cover geometry

The regular action gives actual automorphisms of `Z_G=Spec(ℂ^G)` over
`Spec ℂ`. The bijection `(a,x)↦(x,a*x)` induces an isomorphism of actual
schemes

```text
Z_(G×G) ≅ Z_G ×_(Spec ℂ) Z_G.
```

Its two projections are the actual maps with labels `x` and `a*x`.
The actual scheme coproduct `∐ a:G, Z_G ≅ Z_(G×G)` therefore instantiates
the existing `GaloisCollisionDecomposition`, including both graph-sheet
projection equations. The collision isomorphism is constructed, not supplied
as an interface field.

The quotient label map `g↦gD` gives
`Z_G → Z_S → Spec ℂ`. Its actual morphism is finite, étale, and proper,
and commutes with the left `G` actions. The sheet set is identified with
its marked point plus complement by the explicit `Option I ≃ S`; the
associated scheme isomorphism identifies the marked-point component.

## Multiplicative residual Chow map

Define the cycle first, then its class:

```text
residualCycles(x) = ∑ i:I, x(i) • [the actual integral point subscheme i],
λ_D(x) = classMap(residualCycles(x)) ∈ CH_0(Z_I;ℚ).
```

Restriction to the complementary sheets is an equivalence with inverse
zero extension at the marked sheet. The actual Chow point-coordinate
theorem upgrades the same geometric map to a linear equivalence. It proves

```text
λ_D(x*y) = λ_D(x) · λ_D(y),
z_D := λ_D(a_D) = −[Z_I],
[Z_I] = ∑ i:I, [i].
```

The product on the right is geometric Chow intersection, not correspondence
convolution. No inverse Betti map or selected representative of an arbitrary
Hodge class defines `λ_D`.

The independently constructed cycle-class equivalence gives

```text
θ_D = cl_I ∘ λ_D : E_D ≃ₗ[ℚ] H_I,
α_D = θ_D(a_D) = −cl_I[Z_I].
```

The same operation compatibility makes this map multiplicative for
degree-zero cup product. Its bijectivity is proved from the two existing
equivalences, not assumed in the comparison.

## Actual diagonal source and Chow shear

Actual point-cycle assembly followed by proper diagonal pushforward gives
an injective algebra map from sheet functions into the Chow correspondence
algebra. Its coefficients are the diagonal matrix of that function. Thus a
characteristic sheet maps to the actual point-pair correspondence.

On the actual Tate block `Z_(Option I)`, retain the fixed action `ρ_I⁺`
from checkpoint 0014. Let `e_*=[(*,*)]`, and use the same actual column map
`j(i)=(*,i)` as the graph construction:

```text
N_z = j_*z,
𝒰_z = 1 + N_z,
N_z N_w = 0,
𝒰_z⁻¹ = 𝒰_(-z),
𝒰_z e_* 𝒰_(-z) = enc_I(z).
```

Here multiplication is the actual geometric Chow correspondence composition.
The column is canonical shared data with `SplitChowTateBlock.encode`;
the new module does not define a second graph encoding. The actual Betti
representation sends `𝒰_z` to the linear shear
`U_cl(z)(t,h)=(t,h+t·cl(z))`.

Reindexing the sheet functions, applying the actual diagonal embedding, and
conjugating by `𝒰_(z_D)` gives an injective algebra map
`δ_D^mk:A_D→Γ_(I⁺)^CH`. The actual marked projector is defined as the
image `Π_D=δ_D^mk(q_D)` and proved equal to
`𝒰_(z_D)e_*𝒰_(-z_D)`. It is idempotent and
realizes `P_(α_D)` under the original fixed target action. The raw marked
point `e_*` and its conjugate `Π_D` remain distinct objects.

## Marked action and lower-left detection

The source uses the constant-unit decomposition
`T_D(f)=(f(s₀), f−f(s₀)·1)`. With `Θ_D=id_ℚ⊕θ_D`, its realized
coordinates are

```text
Θ_D T_D(f) = (f(s₀), cl_I(∑ i:I, (f(i)−f(s₀)) [i])).
```

Subtracting the marked constant is the shear by `α_D`, since its point
coefficients are all `−1`. This matches the actual geometric Chow shear
and the actual sheet-cohomology map. The latter is itself constructed from
the full actual weighted point-cycle sum followed by cycle class, and
`sourceToBlock_eq_realization_shear` proves the coordinate identification.
It gives

```text
ρ_I⁺(δ_D^mk(f))(Θ_D T_D(g)) = Θ_D T_D(f*g),
ρ_I⁺(Π_D) Θ_D = Θ_D (T_D m_(q_D) T_D⁻¹),
ρ_I⁺(Π_D) = P_(α_D),
dec_I(Π_D) = z_D,
cl_I(dec_I(Π_D)) = α_D,
ρ_I⁺ ∘ φ_(Π_D) = φ_(P_(α_D)).
```

The constructed residual map and selector square instantiate the canonical
restriction-free `MarkedProjectorActionComparison`. The generated target
class was fixed by actual source data before the comparison was proved.
The final equality is between algebra homomorphisms from the universal
one-idempotent algebra `ℚ×ℚ`.

## Source match and exact scope

- [Stacks, Example 58.5.1, Tag 0BN8](https://stacks.math.columbia.edu/tag/0BN8)
  identifies finite étale schemes over an algebraically closed point with
  finite sets. The present maps and pullbacks are constructed on the actual
  split schemes rather than inferred from a source axiom.
- [Definition 39.11.1, Tag 0498](https://stacks.math.columbia.edu/tag/0498)
  and [Definition 39.11.3, Tag 049A](https://stacks.math.columbia.edu/tag/049A)
  provide the trivial constant-group torsor convention. The project's
  collision projections use `(x,a*x)` rather than `(a*x,x)`; the two actual
  projection identities record this convention explicitly.
- [Section 58.7, Tag 03SF](https://stacks.math.columbia.edu/tag/03SF)
  requires connectedness for its term Galois cover. This split torsor has
  disconnected source when `G` is nontrivial; it supplies no normal-closure
  datum of fields.
- The homogeneous set `G/D` requires no normality of `D`. For comparison,
  [Theorem 9.21.7, Tag 09DW](https://stacks.math.columbia.edu/tag/09DW)
  identifies normal subgroups with Galois intermediate extensions in the
  field setting; that additional property is not asserted here.
- Actual cycle operations, correspondence composition, and cycle-class
  normalization retain the exact sources recorded in checkpoints 0012--0014.
  The residual construction, Chow shear, and action square are direct
  project proofs with no additional source axiom.

The shear is an invertible Chow correspondence, not a scheme automorphism.
The schemes here are already proper, so no nontrivial compactification or
purity theorem is being applied. There is no ambient algebra restriction
`Γ^CH→A_D`: the valid diagonal algebra map goes in the opposite direction.

There is a proved algebraic constraint on generalizing this multiplicative
construction. In any marked augmented source, `a=q−1` satisfies `a*x=−x`
on the residual ideal and hence `a²=−a`. If a linear residual map `θ`
also preserves multiplication into a rational algebra, its generated class
obeys `θ(a)·θ(x)=−θ(x)` and `θ(a)²=−θ(a)`. Surjectivity lets one take
`θ(x)=1`, forcing `θ(a)=−1`. Thus arbitrary class coverage cannot follow
by varying surjective multiplicative residual maps alone.

The next task is class-dependent geometric generation beyond this canonical
class, together with non-split or positive-dimensional cover geometry and
any required nontrivial compactification comparison. The general residual
interface is linear; its geometric restrictions and coverage must still be
proved. The already constructed finite degree-zero Hodge target remains a
known finite case, not a new positive-dimensional Hodge result.

## Lean ownership and parity

| Module | Principal objects |
| --- | --- |
| `Correspondence/Examples/SplitGaloisSheets.lean` | `SplitGaloisSheets.regularAction`, `.quotientMap`, `.regularTorsorIso`, `.regularCollisionDecomposition` |
| `Realization/Chow/Examples/SplitGaloisResidual.lean` | `SplitGaloisResidual.Complement`, `.residualCycles`, `.residualChowEquiv`, `.residualChow_mul`, `.residualChow_residualClass` |
| `Realization/Chow/Examples/SplitChowDiagonal.lean` | `SplitChowDiagonal.diagonalAlgHom`, `.matrix_diagonalAlgHom`, `.diagonalAlgHom_injective`, `.diagonalAlgHom_single` |
| `Realization/Chow/Examples/SplitChowShear.lean` | `SplitChowShear.pointProjector`, `.shear`, `.shearUnit`, `.shear_point_shear_neg` |
| `Realization/Betti/Examples/SplitChowShear.lean` | `SplitBettiTateBlock.realization_column_apply`, `.realization_shear` |
| `Realization/Betti/Examples/SplitGaloisMarkedComparison.lean` | `SplitGaloisMarkedComparison.sheetSchemeIso`, `.residualRealization`, `.generatedClass`, `.sourceToBlock_eq_realization_shear`, `.markedEmbedding`, `.markedProjector`, `.comparison`, `.projectorLift`, `.palomarTargetSquare` |
| `Realization/Betti/Examples/SplitGaloisAction.lean` | `SplitGaloisMarkedComparison.markedEmbedding_action`, the full sheet-algebra action comparison |
| `Realization/Chow/MultiplicativeResidualRigidity.lean` | `MarkedAugmentedAlgebra.generatedClass_sq_eq_neg`, `.generatedClass_eq_neg_one_of_surjective` |

Claim A11m and semantic parity item SP25 record this checkpoint. Its new
notation keeps `λ_D`, `θ_D`, `e_*`, `𝒰_z`, `Π_D`, and the fixed `ρ_I⁺`
distinct. The existing affine graph encoding and linear decoder are reused.
Neither the residual equivalence nor the Chow shear is lossy; the earlier
free-span-to-additive-quotient loss remains exactly the point-decomposition
ideal.

## Verification record

- The split cover, residual Chow map, diagonal embedding, actual
  Chow/Betti shears, multiplicative rigidity, marked comparison, and
  full sheet-action modules pass their direct builds.
- Citation-key checks and `git diff --check` pass.
- The full `lake build` and its canonical-cache repeat pass (3024 jobs);
  only the unchanged `Challenge.lean` admitted-statement warnings remain.
- Primary-source matching and independent mathematical review pass.
- The single-PDF build passes: 30 pages, 642484 bytes, with no warnings,
  undefined references, or overfull/underfull boxes in `paper/main.log`.
  Visual review passes on pages 19--20 (the marked theorem/action),
  pages 23--26 (the gap and module map), and page 30 (the bibliography).
- The local `hodgealpha.bst` preserves the standard alpha bibliography
  format and its original license, extending only repeated-label suffixes
  to `a,…,z,aa,…`. A separate 703-reference BibTeX regression verifies
  every label through `zz→aaa`, without warnings. No source author or date
  was changed to avoid the original style's 26-label overflow.
- The complete `research/Verification.lean` harness exits successfully,
  with no warnings or errors. All 24 new axiom reports contain only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Regressions pass for the noncommutative group `S₃` with an explicit
  nonnormal point stabilizer, `D=⊤` with empty complement and zero
  fundamental class, the residual negative sign, singleton diagonal,
  `sourceToBlock(1)=(1,0)`, actual marked-projector decoding, the full action
  of a complementary sheet on the constant function `2`, and the universal
  Palomar square.
