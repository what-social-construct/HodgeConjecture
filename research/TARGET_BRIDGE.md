# Intended target and equivalence bridge

Assessed: 2026-09-14. This is the current target-first sketch, not a second
manuscript or a new theorem. The detailed component status remains in
[GAP_MAP.md](GAP_MAP.md), with theorem scope in [CLAIM_LEDGER.md](CLAIM_LEDGER.md).

## 1. Fix the target before choosing a cover

For a smooth projective complex variety \(X\) and codimension \(p\), put
\(A=\mathrm{CH}^p(X)_{\mathbb Q}\), \(V=H^{2p}(X,\mathbb Q)\), and let
\(V_{\mathrm{Hdg}}\) be the inverse image of \(H^{p,p}(X)\) under
complexification. The intended statement is

\[
  \mathrm{HC}_{\mathbb Q}(X,p):\quad
  \forall\alpha\in V_{\mathrm{Hdg}},\quad
  \exists z\in A,\quad \operatorname{cl}(z)=\alpha.
\]

Hodge membership is specified independently of the cycle-class image.
Write \(\mathscr H=(A,V,V_{\mathrm{Hdg}},\operatorname{cl})\) for these data.
`RationalHodgeCycleClassModel` and `RationalHodgeConjectureAt` in
[`HodgeClasses.lean`](../HodgeConjecture/Realization/HodgeClasses.lean)
record this logical shape. To get the classical universal conjecture, the
family index must cover all smooth projective complex varieties, all
codimensions must be included, and the supplied models must be their actual
geometric data. Those general instances are not constructed here.

## 2. The equivalence already proved in Lean

Fix a rational algebra \(\Gamma\) and action
\(\rho:\Gamma\to\operatorname{End}_{\mathbb Q}(\mathbb Q\oplus V)\).
Geometrically, the marked rational line has Tate type \(\mathbb Q(-p)\);
Lean's block calculation uses its underlying rational module. The required
graded/twisted Chow realization and variance conventions must be justified
in a general instance, not inferred from the block notation.

Define \(P_\alpha(t,x)=(t,t\alpha)\) and
\(d_{\mathrm{ll}}(T)=\operatorname{pr}_V(T(1,0))\). Supply:

- **Construction** \(C:A\to\Gamma\), with \(C(z)^2=C(z)\) and
  \(\rho(C(z))=P_{\operatorname{cl}(z)}\). This is a function, not a
  claimed linear map: its formula includes the marked identity block.
- **Detection** \(D:\Gamma\to_{\mathbb Q} A\), with
  \(\operatorname{cl}(D(\gamma))=d_{\mathrm{ll}}(\rho(\gamma))\).

Then the checked bridge is

\[
  \mathrm{HC}_{\mathbb Q}(\mathscr H)
  \quad\Longleftrightarrow\quad
  \forall\alpha\in V_{\mathrm{Hdg}},\quad
  \exists\Pi\in\Gamma,\quad \Pi^2=\Pi,\quad\rho(\Pi)=P_\alpha.
\]

The forward direction takes \(\Pi=C(z)\) from a cycle representative.
The reverse direction takes \(z=D(\Pi)\). Thus construction is needed for
the forward reformulation; detection alone suffices to turn independently
constructed lifts into the Hodge conclusion. Idempotence of \(P_\alpha\)
holds for every vector and does not itself construct an algebraic lift.

Equivalently, for \(\mathcal U=\mathbb Q\times\mathbb Q\) and
\(\varphi_e(r,s)=re+s(1-e)\), require an idempotent \(\Pi\) with
\(\rho\circ\varphi_\Pi=\varphi_{P_\alpha}\). This is the same target,
not an additional conjecture.

The exact declarations are
`rationalHodgeConjectureAt_iff_everyHodgeClassHasGraphProjectorLift` and
`rationalHodgeConjectureAt_iff_everyHodgeClassHasPalomarTargetSquare` in
[`TateGraphProjector.lean`](../HodgeConjecture/Realization/Chow/TateGraphProjector.lean).
The Hodge-morphism presentation additionally uses
`ClassGraphProjectorHodgeCompatibility`; it is unnecessary when membership
in the independently specified Hodge subspace is used directly.

## 3. Minimal marked route to a prescribed class

Fix \(\alpha\) first. For a marked augmented algebra with selector \(q_H\),
residual ideal \(E_H\), and \(a_H=q_H-1\), seek actual geometric data
\(\Pi\in\Gamma\), \(\theta:E_H\to_{\mathbb Q}V\) satisfying

\[
  \theta(a_H)=\alpha,\qquad
  \rho(\Pi)\Theta=\Theta P_{a_H},\qquad
  \Theta=\operatorname{id}_{\mathbb Q}\oplus\theta.
\]

Evaluating at \((1,0)\) gives the entire needed implication:

\[
  \operatorname{cl}(D(\Pi))
    =d_{\mathrm{ll}}(\rho(\Pi))
    =\theta(a_H)=\alpha.
\]

The operator lemma is
`MarkedProjectorActionComparison.lowerLeftClass_action_eq_generatedClass`;
the Chow bridge is `cycleClass_decode_eq_generatedClass`, with detection
explicit in its signature, both
in [`MarkedAugmentedRealization.lean`](../HodgeConjecture/Realization/Chow/MarkedAugmentedRealization.lean).
This lower-left conclusion does not need surjectivity or idempotence.
Idempotence of \(\Pi\) and surjectivity of \(\theta\) additionally give
the full graph-projector lift and the universal-algebra target square.
Do not impose these stronger requirements just to extract one cycle class.

The marked proof spine follows one chosen algebraic projector \(\Pi\) for
each prescribed \(\alpha\), with its extension data retained:

| Conclusion | Inputs beyond the marked comparison and prescribed-class equality | Lean location |
| --- | --- | --- |
| A cycle \(z=D(\Pi)\) with \(\operatorname{cl}(z)=\alpha\) | Detection | Core `cycleClass_decode_eq_generatedClass` |
| The chosen \(\Pi\) as a full graph lift | Its idempotence and residual surjectivity for this cancellation proof | Core `toAlgebraicProjectorLift`; extension specialization uses \(\Pi=\Pi_x\) for the chosen witness \(x\) |
| Reverse implication from the Hodge target to the existing marked Galois coverage | Construction and the named replacement hypothesis | `classDependentMarkedGaloisSelectorCoverage_of_everyHodgeClassHasGraphProjectorLift` |

The projector-lift conclusion keeps exactly the chosen element. Its
extension data and witness \(x\) must remain available separately, since
an ordinary `AlgebraicProjectorLift` does not store them. A genuine geometric
extension instance remains to be constructed in the general setting.
Construction \(C\) is retained for the Hodge-to-graph direction of the
equivalence, not as a second projector in the marked construction.

The Galois replacement hypothesis asserts existence of some structured
witness for the same class, not equality with a particular input projector.
It is not an identity-preserving conversion. The full Galois equivalence
therefore retains an additional obligation beyond the graph equivalence.

The chosen algebra, maps, and action square must come from geometry. In
particular, choosing a Chow representative of \(\alpha\) to build them
would assume the desired conclusion. If a geometric factorization
\(\theta=\operatorname{cl}\circ r_{\mathrm{CH}}\) is constructed and
\(\theta(a_H)=\alpha\) is proved, then \(r_{\mathrm{CH}}(a_H)\) already
is the requested cycle; no further operator argument is necessary.

## 4. Where actual construction is missing

| Obligation | Present status | Exact task |
| --- | --- | --- |
| Genuine target and block detection | Constructed for finite split degree zero | Construct the general geometric model, correspondence action, and detection law; construct the encoding for the full equivalence |
| Class-dependent geometric generation | Canonical marked example gives \(-\operatorname{cl}[Z_I]\) | For a prescribed Hodge \(\alpha\), build genuine data and prove \(\theta(a_H)=\alpha\), without assuming its algebraicity |
| Geometric action comparison | Constructed for that finite split example | Prove the displayed action square for the newly constructed data |
| Extension, when the chosen construction needs a boundary | Local fixed-ring results and conditional input consumers; actual closed-graph and integral-cycle restriction for a supplied finite étale extension | Instantiate the relevant purity/gluing maps. Next construct dimension-controlled Chow composition/descent and general component cycles; for the stronger projector route, construct the graph algebra maps, or correct a raw closure and prove its idempotence |
| All-class and universal quantifiers | Abstract schemas only beyond the finite case | Make the construction work for every prescribed class in every intended geometric model |

The finite split target itself has graph lifts for every degree-zero class;
the canonical marked Galois construction is the narrower fixed-class result.
Its residual map is an actual equivalence, not a lossy projection.

The commutative-algebra localization branch concerns local rings, fixed
rings, and inertia. It feeds the extension obligation only after the geometric
comparison and global extension hypotheses have been justified. For a raw
lift \(\Pi_0\) of a generic idempotent, Chow localization places
\(\Pi_0^2-\Pi_0\) in a boundary image, given a separately justified
algebra restriction and exactness for that same map. Boundary support is
not defect vanishing.
Neither conclusion supplies the prescribed-class action square by itself.

The stronger existing Galois coverage schemas retain additional extension
data. Their converses require named replacement/factorization hypotheses.
Those hypotheses are not needed for the forward Hodge implication and are
not part of the basic graph-projector equivalence.

## 5. Bench and next checkpoint

The standalone matrix-restriction diagnostic is preserved on the
[object bench](bench/README.md), outside active imports and manuscript claims.
It is not an obstruction assumed by this sketch. No choice of \(\Gamma\)
as a full matrix algebra, and no ambient restriction to commutative sheets,
is required by the core action comparison. Actual finite Chow matrix
coordinates remain where their verified constructions use them.

At the preceding bench/reorganization checkpoint, the full Lean build,
all 100 active axiom reports, the proof-dependency
audit, and the single manuscript PDF build passed after the bench move.
The two chosen-projector regression checks retain the original element and
its supplied restriction law; the auxiliary bench source also checks
separately. These checks concern the statements and their placement, not
geometric instances of the obligations in the table above.

## 6. Construction-first plan

Keep the existing target equivalence fixed. Work toward its geometric
instance, with one chosen projector for each prescribed class. The
closed-graph/restriction checkpoint is constructed at scheme level, and
integral graph generators now have finite-cycle and open-restriction maps.
Their composition intersection and image are identified as actual schemes;
integral fundamental multiplicity is computed over the ambient stalk.
The class-generation theorem is a separate mathematical obligation and must
be developed alongside that infrastructure.

1. **Closed graph subschemes and open restriction: scheme-level checkpoint
   constructed.** For a separated structural morphism,
   [`GraphSubscheme.lean`](../HodgeConjecture/Correspondence/GraphSubscheme.lean)
   constructs `graphMorphism`, its kernel `graphIdeal`, and
   `graphSubschemeIso`. The graph is a closed immersion and hence proper as
   a morphism to the relative product. Given an actual finite étale
   extension `E` over an open \(j:U\hookrightarrow S\), with inclusion
   \(\iota:Y\to\bar Y\),
   [`GraphRestriction.lean`](../HodgeConjecture/Boundary/GraphRestriction.lean)
   constructs the open pair inclusion \(\iota^{(2)}\), proves
   `graphRestriction_isPullback`, and proves the actual ideal equality
   \[
     \mathcal I_{\sigma_U}
       =(\iota^{(2)})^*\mathcal I_\sigma
   \]
   in `graphIdeal_restriction`, where \(\sigma_U=E.\mathrm{restriction}(\sigma)\).
   Here the graph morphism is \(g_\sigma=(\mathrm{id},\sigma)\), its closed
   subscheme is \(\operatorname{Gr}(\sigma)\), and \(\mathcal I_\sigma\)
   is its defining ideal; inverse image is `IdealSheafData.comap`.
   Restricting an already extended automorphism needs no
   `DeckExtensionHypothesis`. The corollary `graphIdeal_liftDeckAction`
   uses that explicit hypothesis only to lift a prescribed original action.
   **Established:** actual schemes, closed immersions, and scheme-theoretic
   base change, without finite point labels. Constructing the extension in
   the intended geometric application remains a separate input obligation.

2. **Cycle assembly and open restriction, then the correspondence algebra.**
   `Cycles/Basic.lean` defines finite, ungraded cycles on actual integral
   ideal-sheaf subschemes; the earlier finite split cycle types reuse this
   definition. `Cycles/OpenRestriction.lean` restricts each integral
   generator by actual ideal-sheaf inverse image, returning zero for an
   empty intersection. A nonempty inverse image is proved integral.
   `Correspondence/GraphCycles.lean` makes an integral source's closed graph
   into such a generator, proves its dimension agrees with the source via
   the graph isomorphism, and linearly assembles rational graph sums.
   `Boundary/GraphCycleRestriction.lean` connects these constructions to
   the supplied extension: restriction commutes with graph-cycle assembly
   and with the induced rational deck-group map. The nonempty original
   cover is integral because it is open in the integral extended cover.
   These are cycle-level statements, not a Chow algebra or its realization.

   **Next:** establish the dimension and cycle-theoretic hypotheses needed
   for the selected relative correspondence theory, pass to rational
   equivalence, and prove diagonal,
   composition, and restriction compatibility using the geometric
   operations. Specify the admissible relative or support-controlled
   algebra on which restriction is multiplicative; do not assume this for
   every absolute correspondence. Aim to instantiate
   `CompactifiedDeckGraphComparison` in
   [`CompactifiedGraphProjector.lean`](../HodgeConjecture/Boundary/CompactifiedGraphProjector.lean).
   Its current fields require cycle maps on the indicated full finite-étale
   span algebras; a graph-generator construction alone must not be reported
   as an instance of that stronger interface. **Acceptance:** actual cycle
   maps and a proved restriction square on the stated source, yielding
   idempotence of the chosen group-algebra image. If the graph route cannot
   be realized, separately assess raw closure and defect correction;
   boundary support alone is insufficient.

   Keep the current cycle layer ungraded: an open subset need not preserve
   absolute Krull dimension. Matching a dimension grading requires its own
   geometric hypotheses. Graphs with nonintegral carriers also need actual
   component cycles and multiplicities, not an assumed coefficient-one
   formula. In particular, finite étaleness alone does not make the base or
   cover reduced. The cycle-restriction proof introduces neither a Chow
   quotient by chosen equations nor an assumed convolution law.

   **Scheme-theoretic composition checkpoint:**
   `Correspondence/GraphComposition.lean` realizes the relative triple
   product as the fiber product of the two relative pairs over their middle
   coordinate. The actual ideal
   \[
     \mathcal J_{\sigma,\tau}
       =p_{12}^*\mathcal I_\tau+p_{23}^*\mathcal I_\sigma
   \]
   defines an intersection isomorphic to the source by
   \(y\mapsto(y,\tau y,\sigma(\tau y))\). Its first/last projection
   is isomorphic onto \(\operatorname{Gr}(\sigma\tau)\), with equality
   of scheme-theoretic image ideals. Only separatedness is used; no
   commutativity of the deck group is assumed.
   `Cycles/IntegralMultiplicity.lean` separately proves that an integral
   closed subscheme has generic stalk length one over the **ambient** stalk,
   using its actual closed-immersion stalk map. This is the coefficient in
   the integral fundamental cycle, not a Chow intersection multiplicity law.

   **Graph-slice cycle pull–push checkpoint:** `Cycles/ClosedImmersionPushforward.lean`
   constructs actual integral image supports and degree-one image cycles;
   the global closed-immersion map is linear and functorial. The generic
   residue-degree proof is now canonical in `Cycles/ResidueDegree.lean`,
   with the older split-point name retained as an adapter. For
   \(W=Y\times_S Y\), `Correspondence/GraphSlice.lean` constructs
   \(s_\tau:W\to T\), \((y,z)\mapsto(y,\tau y,z)\), identifies its
   image with \(p_{12}^{-1}\operatorname{Gr}(\tau)\), and proves that
   \(u_\tau=p_{23}s_\tau\) is the pair isomorphism \((\tau,\mathrm{id})\).
   The actual cycle maps in `GraphCycleComposition.lean` satisfy
   \[
     \mathsf R_\tau[\operatorname{Gr}(\sigma)]
       =[\operatorname{Gr}(\sigma\tau)],\qquad
     \mathsf K_\tau[\operatorname{Gr}(\sigma)]=[Z_{\sigma,\tau}],
   \]
   where \(\mathsf R_\tau=u_\tau^*{}_{\mathrm{cyc}}\) and
   \(\mathsf K_\tau=s_{\tau,*\mathrm{cyc}}\mathsf R_\tau\).
   The supportwise outer image of \([Z_{\sigma,\tau}]\) is
   \([\operatorname{Gr}(\sigma\tau)]\), with its actual residue degree one.
   The first two maps extend linearly. No integral generator is assigned
   to either possibly reducible inverse-image graph subscheme.
   Étaleness makes these graph and slice inclusions open as well as closed.

   **Structural-base comparison checkpoint (A11s / SP34):** for
   \(p:Y\to S\), \(b:S\to B\), \(r=b\circ p\),
   `DeckBaseChange.lean` retains the actual automorphism through an
   injective group homomorphism, denoted \(\sigma\mapsto\bar\sigma\).
   `RelativeProductComparison.lean` constructs closed pair and triple
   inclusions \(\kappa_2:W_p\to W_r\), \(\kappa_3:T_p\to T_r\)
   when \(b\) is separated. `GraphBaseComparison.lean` proves actual
   morphism, graph-image, and intersection-image compatibility.
   `GraphCycleBaseComparison.lean` proves
   \[
     \kappa_{2,*\mathrm{cyc}}[\operatorname{Gr}_p(\sigma)]
        =[\operatorname{Gr}_r(\bar\sigma)],\qquad
     \kappa_{3,*\mathrm{cyc}}[Z^p_{\sigma,\tau}]
        =[Z^r_{\bar\sigma,\bar\tau}],
   \]
   with separated \(p,b\) and integral \(Y\), including the rational
   weighted graph-assembly square. On all finite cycles the comparison
   pushforwards also intertwine \(\mathsf R\) and \(\mathsf K\),
   without an integrality premise. `Cycles/IsomorphismTransport.lean`
   proves this through genuine isomorphism pullback and inverse closed
   pushforward. For \(B=\operatorname{Spec}k\), the destination pair
   and triple are the absolute products; their cycle comparison is now
   constructed, not merely a proposed identification.

   **Local coefficient checkpoint (A11t / SP35):** `Cycles/LocalOrder.lean`
   uses the existing quotient-length order on fraction fields, restricted
   to units, to obtain signed integers. It proves finite quotient lengths,
   numerator-minus-denominator, product/inverse laws, and vanishing for
   local units. `LocalOrderTransport.lean` proves ring/field-isomorphism
   invariance. `FunctionFieldTransport.lean` constructs the actual
   contravariant function-field map of a scheme isomorphism and its square
   with each stalk map. `SchemeLocalOrder.lean` constructs the point index
   \(\operatorname{DivPt}(X)=\{x:\dim\mathcal O_{X,x}=1\}\), including
   points obtained from height-one primes in an affine chart, and proves
   \(\operatorname{ord}_x(e^*f)=\operatorname{ord}_{e_1(x)}(f)\).
   The scheme-order construction needs integral locally Noetherian schemes,
   not normality or DVRs. This checkpoint proves the actual local
   coefficients; the principal-divisor cycle is assembled in A11w / SP38.

   **Closed support checkpoint (A11u / SP36):** `Cycles/PointSupport.lean`
   constructs the actual reduced closure \(Z_x\) of every scheme point,
   with inverse \(\xi_Z=\iota_Z(\eta_Z)\) on the existing integral
   ideal-sheaf subschemes. `SupportCodimension.lean` identifies chain
   codimension with the dimension of the actual local ring.
   `DivisorSupport.lean` restricts the equivalence to
   \(\operatorname{DivPt}(X)\simeq\operatorname{PrimeDiv}(X)\), where
   prime divisors are a subtype of the existing cycle generators.
   Its isomorphism transport is proved equal to the existing ideal-sheaf
   image, and the signed local-order comparison holds on these supports.
   This identification needs no integral or Noetherian ambient hypothesis;
   the local coefficients retain their integral locally Noetherian domain.

   **Finiteness checkpoint (A11v / SP37):** `Cycles/HeightOneFiniteness.lean`
   proves that height-one primes containing a nonzero element are minimal
   over its principal ideal and form a finite set in a Noetherian domain
   of arbitrary dimension. `RationalFunctionPresentation.lean` expresses
   each actual rational function by nonzero sections on any nonempty affine
   chart and proves that its coefficient vanishes where both germs are
   units. `DivisorFiniteness.lean` gives a finite affine bound and uses the
   generic-point/open-set equivalence to prove local finiteness of the
   actual closed supports. Quasi-compactness then gives finite support in
   both the existing point and prime-divisor presentations. No normality,
   properness, or finiteness of the whole prime-divisor index is assumed.

   **Principal-divisor checkpoint (A11w / SP38):**
   `Cycles/PrincipalDivisor.lean` assembles the finite sum in the existing
   `Cycles X ℤ`, with the existing local order at prime divisors and zero
   elsewhere. It proves its exact support and product/inverse/quotient
   laws, and bundles the multiplicative-to-additive homomorphism.
   `IsomorphismTransport.lean` identifies the existing pushforward with
   reindexing through actual image supports. `PrincipalDivisorTransport.lean`
   proves both pushforward and existing open-restriction identities through
   a scheme isomorphism and its actual contravariant function-field map.
   Integral locally Noetherian quasi-compact hypotheses are explicit;
   no relation package or new cycle module is supplied.

   **Dimension-function checkpoint (A11x / SP39):**
   `Cycles/DimensionFunction.lean` retains both conditions of the standard
   dimension-function definition on actual points. Support degree is
   \(\delta(\xi_Z)\); prime codimension implies immediate specialization
   and hence degree \(\delta(\eta)-1\).
   `DimensionFunctionRestriction.lean` constructs actual closed-immersion
   restriction and proves degree agreement with the actual closed image.
   `CycleDegree.lean` selects homogeneous submodules of the existing cycles,
   not another free module. `PrincipalDivisorDegree.lean` proves the
   principal cycle homogeneous and shows that pushing from an integral
   closed carrier \(W\) gives ambient degree \(\deg_\delta(W)-1\).
   Only that carrier needs local Noetherianity and quasi-compactness;
   the ambient scheme need not be integral. The dimension function remains
   an explicit parameter, not a theorem of existence for every scheme.

   **Principal-relation checkpoint (A11y / SP40):** on Noetherian schemes
   with an explicit dimension function, `PrincipalRelations.lean`
   generates relations from actual degree-\(n+1\) integral carriers
   and their function-field units. Span membership is equivalent to an
   unweighted finite sum of actual ambient principal cycles, using powers
   to absorb integer coefficients. Locally finite **carrier** families
   are finite on the chosen quasi-compact domain, even when their
   principal cycles vanish, so the finite relation convention matches
   the source. The resulting quotient is \(\mathrm{CH}_n^\delta\).
   `PrincipalDivisorImage.lean` transports each principal image through
   the actual closed support-to-image function-field isomorphism;
   `GradedPushforward.lean` restricts the existing geometric cycle map.
   `ChowPushforward.lean` proves generator and submodule preservation,
   then quotient descent, the representative square and identity/composition.
   `ChowIsomorphism.lean` gives the actual quotient isomorphism, whose
   inverse on cycles is the existing open restriction along the isomorphism.
   Actual dimension-function restriction discharges the degree comparison;
   no freely chosen relation submodule or relation-preservation premise is used.

   **Geometric-dimension checkpoint (A11z / SP41):**
   `SupportDimension.lean` proves that an actual integral carrier has
   dimension equal to the height of its ambient generic point. On a
   finite-dimensional scheme, point-closure height is a finite integer
   and strictly increases along proper generization.
   `FiniteTypeDimension.lean` proves a finite polynomial-presentation
   bound and finite dimension for finite-type algebras over a field;
   `FiniteTypeSchemeDimension.lean` extends this to actual finite-type
   schemes using a finite affine subcover and the stalk-isomorphism
   comparison for point coheight. Neither an exact polynomial dimension
   formula nor a dimension-function law is assumed.
   `LowDimensionalDimensionFunction.lean` constructs the actual
   \(\delta_X(x)=\dim\overline{\{x\}}\) when \(\dim X\leq1\),
   proving both laws from the dimension bound and identifying the existing
   support degree with actual carrier dimension. The affine-line example
   has dimension one, generic-point degree one and origin degree zero.
   This supplies a genuine bounded grading instance for SP40, not the
   general finite-type dimension-function construction.

   **Affine-dimension checkpoint (A11aa / SP42):**
   `TranscendenceDegreeDrop.lean` proves strict drop under actual
   noninjective surjections of domains with finite transcendence degree.
   Applied to prime quotients, this gives a prime-chain upper bound.
   `IntegralDimension.lean` proves dimension invariance using actual
   contraction and chain lifting; `NormalizationDimension.lean` uses
   Noether normalization and the proved polynomial lower bound for the
   independent opposite inequality. `AffineDimension.lean` therefore
   proves \(\dim A=\operatorname{trdeg}_k\operatorname{Frac}(A)\)
   for finite-type domains, and the sharp field-polynomial dimension
   formula. `AffineSupportDimension.lean` identifies the dimension of
   the existing actual reduced carrier of a point of
   \(\operatorname{Spec}A\) with \(\operatorname{trdeg}_k\kappa(p)\),
   where \(\kappa(p)\) is the actual prime-localization residue field.
   This last result allows reducible ambient algebras and also identifies
   the integer scheme-point height. No immediate-specialization law or
   dimension-function package is supplied as a hypothesis.

   **Polynomial-local checkpoint (A11ab / SP43):**
   `PolynomialPrimeHeight.lean` constructs prime extension along the actual
   constant-polynomial map, proves contraction recovers the original prime,
   and proves the extended contraction is strictly below any maximal ideal.
   This gives \(\operatorname{ht}(m\cap R)+1\leq\operatorname{ht}(m)\)
   for every commutative ring. `PolynomialMaximalHeight.lean` combines
   Jacobson maximal contraction, variable induction and SP42's independent
   upper bound to prove
   \(\operatorname{ht}(m)=\dim k[T_1,\ldots,T_n]_m=n\) for every maximal
   ideal over any field, including \(n=0\). No rational-point assumption is
   needed. `PolynomialClosedPointDimension.lean` identifies the actual
   closed-point stalk dimension and scheme-point coheight with \(n\).
   This is not the closed carrier's dimension, which is zero, and does not
   claim regularity, generators or uniform saturated-chain lengths.

   **Normal-base/local-dimension checkpoint (A11ac / SP44):**
   `IntegralIdealPolynomial.lean` constructs ideal-controlled monic
   annihilators in any integral algebra, using an actual finite integral
   subalgebra. `MonicPrimeCoefficients.lean` controls monic-divisor
   coefficients after reduction modulo a prime and scalar substitution.
   `NormalGoingDown.lean` uses actual minimal polynomials to prove
   cancellation, then constructs a prime below the prescribed terminal
   prime. Thus integral injections of domains over an integrally closed
   base have going down, with no separability, Noetherianity or
   target-normality premise and no assumed going-down input.
   `NormalizationLocalDimension.lean` reuses the existing going-down
   height bound and integral incomparability to compare actual heights.
   Polynomial-base normality and SP43's maximal heights give
   \(\operatorname{ht}(m)=s\) through an actual polynomial normalization.
   Every finite-type domain therefore satisfies
   \(\dim A_m=\dim A=\operatorname{trdeg}_k\operatorname{Frac}(A)\)
   at every maximal ideal. `AffineClosedPointDimension.lean` identifies
   actual closed-point stalk dimensions and scheme-point coheights.
   Neither normality of \(A\) nor rationality of the closed point is needed.
   Integrality of the selected local-ring map is not assumed.

   **Residue-localization checkpoint (A11ad / SP45):**
   `ResidueNormalizationLift.lean` lifts an actual polynomial normalization
   of \(B/q\) through the quotient map, with an exact commuting square
   and denominators disjoint from \(q\). `GenericFiberAlgebra.lean`
   constructs the canonical \(K=\operatorname{Frac}(P)\)-algebra on
   \(B'=f(P\setminus\{0\})^{-1}B\), with scalar compatibility and
   finite type from the actual localization pushout.
   `ResidueLocalization.lean` proves the extended prime \(q'\) maximal
   via the actual localized quotient field and its exact kernel. It also
   proves contraction to \(q\) and unchanged height; these comparisons
   do not need integrality. `ResidueNormalizationLocalization.lean`
   supplies the full existential construction for any finite-type algebra,
   without requiring the ambient ring to be a domain. For domain \(B\),
   SP44 further gives \(\operatorname{ht}_B(q)=\operatorname{trdeg}_K B'\).
   Integrality concerns \(P\to B/q\), not the lifted \(P\to B\).

   **Original-field prime-formula checkpoint (A11ae / SP46):**
   `LocalizationTranscendenceDegree.lean` proves full cardinal invariance
   under actual domain localization, with universe-general and numeric
   forms and no finite-type assumption. `AffinePrimeDimension.lean`
   combines that comparison with the canonical polynomial fraction-field
   tower to prove \(n+\operatorname{trdeg}_K B'=\operatorname{trdeg}_k B\).
   The rational function field's finite transcendence degree comes from \(n\), not
   from a false finite-type hypothesis over \(k\). SP45 and the actual
   quotient normalization now give
   \(\operatorname{ht}_B(q)+\operatorname{trdeg}_k(B/q)=\operatorname{trdeg}_k B\)
   for every prime of a finite-type domain. Ordinary height, the actual
   prime-localization residue field, quotient dimension, and the actual
   local-ring formula \(\dim B_q+\dim(B/q)=\dim B\) are also proved.
   No normality, rationality, characteristic-zero or maximality premise
   is added. The domain condition on this global formula is explicit.

   **Consecutive-prime checkpoint (A11af / SP47):**
   `PrimeQuotientCover.lean` transports a prime-spectrum cover
   \(p\lessdot q\) through the actual quotient correspondence,
   proving \(0\lessdot q/p\) and \(\operatorname{ht}_{B/p}(q/p)=1\)
   over any commutative ring. No domain or Noetherianity of \(B\)
   is assumed, and the cover is not taken in the full ideal lattice.
   `ConsecutivePrimeDimension.lean` applies SP46 to \(B/p\) and the
   actual double-quotient \(k\)-algebra equivalence, giving
   \(\operatorname{trdeg}_k(B/q)+1=\operatorname{trdeg}_k(B/p)\).
   The actual prime-residue-field and quotient-dimension versions are
   also proved. This works for reducible or nonreduced finite-type
   algebras, without asserting an ambient stalk-dimension increment.

   **Affine dimension-function checkpoint (A11ag / SP48):**
   `AffineDimensionFunction.lean` combines strict prime-residue degree drop,
   SP47 and the reused `specPointOrderIso` into the existing dimension-function
   structure on literal \(\operatorname{Spec}A\). Both laws are proved,
   and its value equals actual finite point-closure dimension.
   `AffineSchemeDimensionFunction.lean` extracts the finite-type sections
   algebra from an actual affine structural morphism
   \(p:X\to\operatorname{Spec}k\) and transports through `X.isoSpec`
   using existing closed-immersion restriction. Its function is literally
   integer point height. No separate sections algebra or grading-law input
   is required. The actual support-degree and fundamental-cycle membership
   tests identify geometric dimension, also on reducible or nonreduced
   ambient affine schemes and without a dimension-at-most-one bound.

   **Structural residue-field checkpoint (A11ah / SP49):**
   `StructuralResidueField.lean` derives the base action on the actual
   scheme residue field by pulling back and evaluating global constants.
   The action is independently defined and locally installed. Naturality
   proves that actual residue maps are base-algebra maps; actual open
   immersions give base-algebra equivalences. `AffineResidueField.lean`
   constructs the stalk-induced comparison with `Ideal.ResidueField`,
   proves its equality on every \(A\)-constant, and upgrades it to an
   algebra equivalence over any commutative base. Over a field,
   `AffineResidueFieldDimension.lean` preserves full transcendence degree,
   proves its finiteness for a finite-type ambient algebra, and identifies
   the existing literal-spectrum dimension function with actual scheme
   residue degree. It also proves full-cardinal invariance under arbitrary
   open immersions. No finite-type hypothesis on residue fields is asserted.

   **Structural affine-value checkpoint (A11ai / SP50):**
   `AffineSchemeResidueDegree.lean` proves finite structural residue degree
   on every actual affine \(X\) with locally finite-type \(p\) and
   identifies it with the existing `ofAffineLocallyOfFiniteType` value.
   The proof extracts the actual finite-type sections algebra, retains
   the spectrum-morphism equality and checks the composite with
   `X.isoSpec.hom` is the original \(p\). Thus SP49 transports the
   actual structural action, not just the field carrier. The existing
   `point_height_iso` is exposed unchanged and reused. No second dimension
   function or preinstalled sections algebra is introduced. The affine
   values agree under every open immersion between affine schemes over
   this field, using the pulled-back source structural map.

   **Chartwise value checkpoint (A11aj / SP51):**
   `ChartResidueDegree.lean` proves finite structural residue degree at
   every point of an arbitrary locally finite-type \(k\)-scheme using
   one actual affine chart. Neither ambient affineness, quasi-compactness,
   a finite subcover nor a global dimension bound is required. For any
   affine open chart, its existing dimension value equals the actual
   structural residue degree at its ambient image. Two chart values
   therefore agree when their actual ambient images agree. The
   point-dependent scalar action is retained throughout; no global
   dimension-function object is introduced by these value theorems.

   **Global dimension-function checkpoint (A11ak / SP52):**
   `FieldDimensionFunction.lean` constructs the actual structural
   residue-degree function on every locally finite-type \(k\)-scheme.
   An affine neighbourhood of the specialized point contains the
   generizing point. Specialization reflection through the actual open
   embedding transfers strict order and the cover relation into that
   chart. SP51's value comparison and the existing affine laws
   prove global strictness and the immediate-specialization unit step.
   The function is nonnegative, equals the existing affine construction
   as a whole object, and has compatible values under arbitrary open
   immersions over the field. No affine, quasi-compact or integral
   ambient premise or supplied gluing package is used.

   **Global height/carrier checkpoint (A11al / SP53):**
   `FieldSupportDimension.lean` identifies the constructed function with
   actual point height and reduced point-closure dimension. Nonnegative
   strictness supplies the upper bound; one actual affine chart, finite
   affine height and the proved normalization supply the lower bound.
   Each point height and each integral closed carrier dimension is finite
   without a global bound, quasi-compactness or Noetherianity of \(X\).
   The existing support degree is its actual carrier dimension, and
   fundamental-cycle membership in natural degree \(n\) is equivalent
   to dimension \(n\) for nontrivial coefficients. Actual open immersions
   preserve point height in this locally finite-type field setting.

   **Next bounded obligation:** start with actual integral \(X\), set
   \(d=\delta_{X/k}(\eta_X)\), and prove finite chain codimension and
   \(\operatorname{codim}_X W+\deg_{\delta_{X/k}}W=d\).
   The generic-point height comparison gives finite integral ambient
   dimension; induction on finite coheight using the existing unit-step
   law provides a route without a supplied uniform-chain theorem.
   Then identify codimension \(p\) with degree \(d-p\) in the existing
   cycle grading. A pure-dimensional or componentwise extension is needed
   for reducible targets; smoothness alone does not make all connected
   components have the same dimension. The current integral quotient's
   Noetherian premise is retained. Construct rational coefficient extension of this
   general integral quotient and the comparison with the target's rational
   Chow groups; the earlier split-case scalar extension is not that theorem.
   General proper pushforward still needs its norm
   compatibility; arbitrary open restriction and flat/Gysin operations
   need their own principal-relation comparisons and quotient descent.
   Absolute
   relations may use larger-dimensional supports outside the relative
   product, so no injectivity on Chow follows from the closed inclusion.
   Establish flat/Gysin comparison and properness
   on the selected domain before promoting `graphCycleLinearMap` to a
   Chow algebra map. No claim that \(r\) is étale follows from étale \(p\).
   The supportwise outer pushforward is proved; an ambient projection map
   on all cycles is not supplied merely by separatedness.

3. **Connect the auxiliary geometry to the prescribed Hodge target.** Fix
   \((X,p,\alpha)\) independently of the cover. Graph correspondences on
   \(\bar Y\) do not automatically act on
   \(\mathbb Q(-p)\oplus H^{2p}(X,\mathbb Q)\). Name the actual geometric
   correspondence or morphism connecting them, with its degree, variance,
   properness, and multiplication compatibilities. Construct the genuine
   target Chow/Betti model and its detection map, then the residual map and
   chosen projector in that target. **Acceptance:** prove
   \(\theta(a_H)=\alpha\) and
   \(\rho(\Pi)\Theta=\Theta P_{a_H}\) from the geometric construction.
   For the full chosen-projector conclusion, prove residual surjectivity
   for the current cancellation argument, or prove the full action equality
   directly. No recipe may begin by choosing a cycle representing
   \(\alpha\). Writing a non-circular candidate for this step is an early
   design gate, not something postponed until the graph infrastructure is
   finished.

4. **Establish coverage and discharge the remaining inputs.** Show that
   the construction works for every prescribed class in the claimed
   geometric family; identify which hypotheses are proved and which remain
   source inputs. The universal Hodge conclusion requires all genuine
   \(X,p\), not just a supplied abstract indexing family. Keep the
   additional Galois replacement theorem separate if the stronger reverse
   coverage equivalence is also sought. **Acceptance:** instantiate the
   existing endpoint using constructed data, with no hypothesis that is
   merely the desired class-generation or realization conclusion renamed.

The immediate work item is step 2's dimension-controlled relative
Chow/composition interface, together with a written candidate for the
comparison in step 3. The graph-intersection and integral-cycle constructions
do not yet construct Chow classes, convolution, or a cohomological action,
and do not by themselves prove that arbitrary Hodge classes come from
those graphs.
