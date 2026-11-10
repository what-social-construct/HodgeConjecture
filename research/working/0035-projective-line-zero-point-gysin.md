# Actual projective-line zero-point Gysin and cycle comparison

Scope checkpoint: 2026-11-07. This continues the actual
[Hodge-filtration checkpoint](0034-projective-line-hodge-filtration.md).
The distinguished zero-point Gysin is constructed through actual relative
singular cohomology. Its unit is the original positive P¹ generator and
the original scheme zero-point cycle class. Both ordinary cycle maps
factor through this actual point Gysin and the existing Chow degree.

## Actual pair kernels and excision

[RelativeCochains.lean](../../HodgeConjecture/Realization/Betti/RelativeCochains.lean)
defines relative rational cochains as the kernel of original restriction
to a singular subcomplex, with the original differential. Extension by
zero proves termwise surjectivity, giving the actual short exact sequence
and its native connecting maps. Exactness, cocycle representatives,
positive lift-and-differentiate formula, original pair pullbacks and
connecting naturality are proved.

[RelativeUnion.lean](../../HodgeConjecture/Realization/Betti/RelativeUnion.lean)
proves strict excision inside the union of two subcomplexes. It glues an
actual relative cochain on the first subcomplex to zero on the second;
the inverse restricts the original cochain. It also retains actual nested
simplex identifications for the intersection and boundary.

[ShortExactQuasiIso.lean](../../HodgeConjecture/Realization/Betti/ShortExactQuasiIso.lean)
uses the native opposite-complex short-exact quasi-isomorphism theorem.
[RelativeExcision.lean](../../HodgeConjecture/Realization/Betti/RelativeExcision.lean)
applies it to the already proved full-to-small singular restriction.
For an actual two-open cover X = U ∪ V this proves

`Hⁿ(X, V; ℚ) ≅ Hⁿ(U, U∩V; ℚ)`.

The forward map is proved to be the original relative restriction.
No excision premise, finite-dimensionality or replacement cohomology is used.

[RelativeMayerVietoris.lean](../../HodgeConjecture/Realization/Betti/RelativeMayerVietoris.lean)
maps the local relative short exact sequence into the existing small
Mayer–Vietoris sequence. The middle map sends `a` to `(a, 0)`; the original
difference is first minus second. Native connecting naturality therefore
gives the positive identity: local relative boundary, inverse actual
excision and forgetting support equal the existing full boundary.

## Actual local orientation and original zero support

[ComplexPointThom.lean](../../HodgeConjecture/Realization/Betti/Examples/ComplexPointThom.lean)
uses actual H²(ℂ, ℂ∖{0}; ℚ). Its Thom class is the native relative boundary
of the original radial pullback of the actual positive circle class.
Its boundary pairing is +1 and its coordinate is 1, so it is nonzero.
Actual singleton H⁰ maps isomorphically to this relative group, sending
the original constant unit to the Thom class.

Forgetting this local class into absolute H²(ℂ) gives zero. The global
construction must retain support through inverse excision; local absolute
cohomology cannot carry this class.

[ProjectiveLinePointSupport.lean](../../HodgeConjecture/Realization/Betti/Examples/ProjectiveLinePointSupport.lean)
proves the original reciprocal chart is exactly P¹ minus the actual
finite zero point. The original evaluation morphism sends that complex
point to the original scheme `projectiveLineZero`. The actual singleton
support retains its topology, original H⁰ and constant-unit class.

[ProjectiveLineNormalChart.lean](../../HodgeConjecture/Realization/Betti/Examples/ProjectiveLineNormalChart.lean)
identifies the original finite-chart singular pair with the actual
complex punctured pair, using the original chart on every simplex.
[ProjectiveLineNormalChartBoundary.lean](../../HodgeConjecture/Realization/Betti/Examples/ProjectiveLineNormalChartBoundary.lean)
uses native pair-boundary naturality to compare the local Thom class
with the actual positive overlap source for P¹ Mayer–Vietoris.

## Geometric Gysin and original ordinary cycles

[ProjectiveLinePointGysin.lean](../../HodgeConjecture/Realization/Betti/ProjectiveLinePointGysin.lean)
constructs the map by the following original maps:

1. Pull actual support H⁰ back to the normal-coordinate singleton.
2. Apply the local oriented Thom isomorphism.
3. Transport the actual relative class through the original finite chart.
4. Use inverse open-cover excision to place it in H² supported at zero.
5. Forget support into actual rational singular H² of P¹.

The complement is the original contractible reciprocal chart, so the
forget-support map is itself an isomorphism in degree two. Native boundary
naturality proves `gysin pointUnit = coverGenerator`, with the original
positive sign. The supported Thom class is nonzero and its global image
is nonzero, despite the local absolute image being zero.

[ProjectiveLineGysinCycleClass.lean](../../HodgeConjecture/Realization/Betti/ProjectiveLineGysinCycleClass.lean)
uses the same original scheme zero to form integral and rational Chow
classes in the existing principal-relation quotients. Both original
ordinary cycle classes equal the geometric Gysin unit. Every ordinary
class then satisfies

`cycleClass z = gysin (pointClass (degree z))`.

The rational statement is an equality of original linear maps; the
integral statement uses the actual integral Chow degree with rational
coefficient extension in the target.

This constructs the distinguished zero-point Gysin in its original finite
chart. It does not construct independent Gysin maps for all closed points,
prove coordinate independence, or identify a general Gysin/Poincaré-dual
cycle map. Those transport comparisons are the next concrete step. A
singular fundamental two-cycle, general comparison, characteristic-zero
degeneration and general prescribed-class generation remain open.

## Validation and build boundaries

Focused targets are `make check-relative-cohomology` and
`make check-projective-line-point-gysin`. They enforce actual kernel and
pair checks, nonzero positive circle excision, local-versus-global
forgetting, original chart and scheme support, rejection of the reversed
orientation and ordinary integral/rational Chow factorization.

The generic relative layers and local complex Thom class exclude project
geometry, cycles, Chow, correspondence, de Rham and sheaf-cohomology sources.
The original projective-line chart retains its existing scheme/cycle
infrastructure. The geometric zero-point Gysin excludes ordinary cycle-map
modules; its comparison layer imports them only afterward. Both branches
exclude de Rham and the assumed Chow-realization layer.

The five focused suites pass 47 examples, 15 named checks and 181 enforced
standard-three axiom audits. The default library build passed 5,099 jobs
at this checkpoint. The root inventory adds checks and axiom reports for
all 208 named declarations in its 11 new modules. All 535 active sources
(534 library modules and the root) passed placeholder scans; all 37
project import boundaries, four indirect-negative guards, dependency pins,
local documentation links and whitespace checks passed. The main README
remained 69 lines at this checkpoint.

The focused zero-point suite and root inventory also pass against the
later working tree. These checks do not replace independent clean-clone
or human release sign-offs. Submission candidate selection and packaging
are unchanged.
