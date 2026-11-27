module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineFiniteSupportComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineRamificationComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineFinitePointComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLinePointGysinComparison
public import HodgeConjecture.MathlibCompat.DeclarationDependencies
public import Mathlib.Tactic.NormNum
public import Lean.Util.CollectAxioms
public import Lean.Util.Path

-- Refresh with: python3 scripts/update_finite_point_audit_imports.py --audit research/ProjectiveLineFiniteSupportGysinVerification.lean
-- BEGIN GENERATED PROJECT PRIVATE IMPORTS
import all HodgeConjecture.Boundary.Normalization.AffineEtaleAlgebra
import all HodgeConjecture.Boundary.Normalization.AffineNormality
import all HodgeConjecture.Boundary.Normalization.AffineNormalizationCoherence
import all HodgeConjecture.Boundary.Normalization.AffineNormalizationDiagram
import all HodgeConjecture.Boundary.Normalization.AffineNormalizationOpenImmersion
import all HodgeConjecture.Boundary.Normalization.AffineNormalizationRestriction
import all HodgeConjecture.Boundary.Normalization.ConjugateBoundary
import all HodgeConjecture.Boundary.Normalization.ConjugateNormalization
import all HodgeConjecture.Boundary.Normalization.DeckAction
import all HodgeConjecture.Boundary.Normalization.EtaleTensorSource
import all HodgeConjecture.Boundary.Normalization.FiniteAffineChart
import all HodgeConjecture.Boundary.Normalization.FiniteAffineCover
import all HodgeConjecture.Boundary.Normalization.FiniteEtaleGluedNormalClosure
import all HodgeConjecture.Boundary.Normalization.FiniteEtaleGluedRefinement
import all HodgeConjecture.Boundary.Normalization.FiniteEtaleNormalClosure
import all HodgeConjecture.Boundary.Normalization.FiniteEtaleNormalClosureRestriction
import all HodgeConjecture.Boundary.Normalization.FiniteFunctionField
import all HodgeConjecture.Boundary.Normalization.FiniteNormalClosure
import all HodgeConjecture.Boundary.Normalization.FixedRingLocalization
import all HodgeConjecture.Boundary.Normalization.FixedRingUnramified
import all HodgeConjecture.Boundary.Normalization.FullVisibleBoundary
import all HodgeConjecture.Boundary.Normalization.FunctionFieldNormalClosure
import all HodgeConjecture.Boundary.Normalization.GluedNormalClosureRefinement
import all HodgeConjecture.Boundary.Normalization.GluedNormalization
import all HodgeConjecture.Boundary.Normalization.GluedNormalizationChart
import all HodgeConjecture.Boundary.Normalization.GluedNormalizationProperties
import all HodgeConjecture.Boundary.Normalization.InertiaDiagram
import all HodgeConjecture.Boundary.Normalization.InvariantIntermediate
import all HodgeConjecture.Boundary.Normalization.Model
import all HodgeConjecture.Boundary.Normalization.NormalClosure
import all HodgeConjecture.Boundary.Normalization.NormalClosureConstruction
import all HodgeConjecture.Boundary.Normalization.NormalClosureFactor
import all HodgeConjecture.Boundary.Normalization.NormalClosureTensor
import all HodgeConjecture.Boundary.Normalization.NormalizationBaseChange
import all HodgeConjecture.Boundary.Normalization.NormalizationIntegralFactor
import all HodgeConjecture.Boundary.Normalization.NormalizationLocalization
import all HodgeConjecture.Boundary.Normalization.NormalizationTensor
import all HodgeConjecture.Boundary.Normalization.PrimeInertia
import all HodgeConjecture.Boundary.Normalization.SeparableFunctionField
import all HodgeConjecture.Boundary.Normalization.ValuationInertia
import all HodgeConjecture.Boundary.Normalization.VisibleRamification
import all HodgeConjecture.Boundary.Sheets.DecompositionSheets
import all HodgeConjecture.Boundary.Sheets.GaloisSheets
import all HodgeConjecture.Boundary.Sheets.InertiaQuotient
import all HodgeConjecture.CommutativeAlgebra.AtPrimeFractionField
import all HodgeConjecture.CommutativeAlgebra.DeRham.Complex
import all HodgeConjecture.CommutativeAlgebra.DeRham.Differential
import all HodgeConjecture.CommutativeAlgebra.FiniteFiberLength
import all HodgeConjecture.CommutativeAlgebra.FiniteLocalization
import all HodgeConjecture.CommutativeAlgebra.FiniteLocalizationFractionField
import all HodgeConjecture.CommutativeAlgebra.FiniteSemilocal
import all HodgeConjecture.CommutativeAlgebra.FiniteTensorProduct
import all HodgeConjecture.CommutativeAlgebra.FlatLocalLength
import all HodgeConjecture.CommutativeAlgebra.FlatLocalMultiplicity
import all HodgeConjecture.CommutativeAlgebra.GenericFiberAlgebra
import all HodgeConjecture.CommutativeAlgebra.IntegralIdealPolynomial
import all HodgeConjecture.CommutativeAlgebra.LatticeIndex
import all HodgeConjecture.CommutativeAlgebra.LocalLength
import all HodgeConjecture.CommutativeAlgebra.LocalizedPrincipalQuotient
import all HodgeConjecture.CommutativeAlgebra.LocalizedResidueDegree
import all HodgeConjecture.CommutativeAlgebra.MonicPrimeCoefficients
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.FiniteSupport
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.HomologicalComplexAbelian
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.MinimalPrimeColength
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.ModuleOrder
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.Multiplication
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.PeriodicAdditivity
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.PeriodicDefs
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.PeriodicLength
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.PrimeFiltration
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.RestrictedDivisors
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.Support
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.SupportLength
import all HodgeConjecture.CommutativeAlgebra.Multiplicity.TwoPeriodic
import all HodgeConjecture.CommutativeAlgebra.NormalGoingDown
import all HodgeConjecture.CommutativeAlgebra.PiTensorBaseChange
import all HodgeConjecture.CommutativeAlgebra.PolynomialSquare
import all HodgeConjecture.CommutativeAlgebra.PrimeQuotientCover
import all HodgeConjecture.CommutativeAlgebra.QuotientLengthBaseChange
import all HodgeConjecture.CommutativeAlgebra.ReducedArtinianFactor
import all HodgeConjecture.CommutativeAlgebra.ResidueLocalization
import all HodgeConjecture.CommutativeAlgebra.SemilocalLength
import all HodgeConjecture.CommutativeAlgebra.SeparabilityTrace
import all HodgeConjecture.CommutativeAlgebra.UnramifiedIntegralFactor
import all HodgeConjecture.Correspondence.Algebra
import all HodgeConjecture.Correspondence.Classes
import all HodgeConjecture.Correspondence.Etale
import all HodgeConjecture.Correspondence.EtaleClasses
import all HodgeConjecture.Correspondence.FiniteGroupProjector
import all HodgeConjecture.Correspondence.Graph
import all HodgeConjecture.Correspondence.Linearized
import all HodgeConjecture.Correspondence.ProjectorLift
import all HodgeConjecture.Correspondence.Scheme
import all HodgeConjecture.Cycles.AffineDimension
import all HodgeConjecture.Cycles.AffineDimensionFunction
import all HodgeConjecture.Cycles.AffinePrimeDimension
import all HodgeConjecture.Cycles.AffineResidueField
import all HodgeConjecture.Cycles.AffineResidueFieldDimension
import all HodgeConjecture.Cycles.AffineSchemeDimensionFunction
import all HodgeConjecture.Cycles.AffineSchemeResidueDegree
import all HodgeConjecture.Cycles.AffineSupportDimension
import all HodgeConjecture.Cycles.Basic
import all HodgeConjecture.Cycles.ChartResidueDegree
import all HodgeConjecture.Cycles.ChowPushforward
import all HodgeConjecture.Cycles.ClosedImmersionPushforward
import all HodgeConjecture.Cycles.CoefficientExtension
import all HodgeConjecture.Cycles.ComponentLocalLength
import all HodgeConjecture.Cycles.ComponentStalk
import all HodgeConjecture.Cycles.ConsecutivePrimeDimension
import all HodgeConjecture.Cycles.CycleDegree
import all HodgeConjecture.Cycles.DimensionFunction
import all HodgeConjecture.Cycles.DimensionFunctionRestriction
import all HodgeConjecture.Cycles.DivisorFiniteness
import all HodgeConjecture.Cycles.DivisorSupport
import all HodgeConjecture.Cycles.EquidimensionalDivisorPoint
import all HodgeConjecture.Cycles.FiberMultiplicityLocal
import all HodgeConjecture.Cycles.FiberResidueField
import all HodgeConjecture.Cycles.FiberStalkKernel
import all HodgeConjecture.Cycles.FieldDimensionFunction
import all HodgeConjecture.Cycles.FieldSupportDimension
import all HodgeConjecture.Cycles.FiniteAffineFiber
import all HodgeConjecture.Cycles.FiniteAffineLocalOrder
import all HodgeConjecture.Cycles.FiniteAffineResidue
import all HodgeConjecture.Cycles.FiniteAffineStalk
import all HodgeConjecture.Cycles.FiniteAffineStalkMap
import all HodgeConjecture.Cycles.FiniteChowPushforward
import all HodgeConjecture.Cycles.FiniteDivisorPoints
import all HodgeConjecture.Cycles.FiniteFiberClosedBaseChange
import all HodgeConjecture.Cycles.FiniteFiberDegree
import all HodgeConjecture.Cycles.FiniteFiberPullback
import all HodgeConjecture.Cycles.FiniteFlatChowDegree
import all HodgeConjecture.Cycles.FiniteFlatChowPullback
import all HodgeConjecture.Cycles.FiniteFlatComponentOrder
import all HodgeConjecture.Cycles.FiniteFlatLocalOrder
import all HodgeConjecture.Cycles.FiniteFlatPrincipalDivisor
import all HodgeConjecture.Cycles.FiniteFlatPrincipalRelations
import all HodgeConjecture.Cycles.FiniteFlatRank
import all HodgeConjecture.Cycles.FiniteGrading
import all HodgeConjecture.Cycles.FiniteLocalizationNorm
import all HodgeConjecture.Cycles.FinitePrincipalDivisor
import all HodgeConjecture.Cycles.FinitePrincipalDivisorImage
import all HodgeConjecture.Cycles.FinitePushforward
import all HodgeConjecture.Cycles.FinitePushforwardCoefficients
import all HodgeConjecture.Cycles.FinitePushforwardComposition
import all HodgeConjecture.Cycles.FinitePushforwardResidue
import all HodgeConjecture.Cycles.FinitePushforwardSquare
import all HodgeConjecture.Cycles.FiniteResidueField
import all HodgeConjecture.Cycles.FiniteSchemeLength
import all HodgeConjecture.Cycles.FiniteTypeDimension
import all HodgeConjecture.Cycles.FiniteTypeSchemeDimension
import all HodgeConjecture.Cycles.FlatComponentFunction
import all HodgeConjecture.Cycles.FlatComponents
import all HodgeConjecture.Cycles.FunctionFieldComparison
import all HodgeConjecture.Cycles.FunctionFieldMap
import all HodgeConjecture.Cycles.FunctionFieldNorm
import all HodgeConjecture.Cycles.FunctionFieldResidue
import all HodgeConjecture.Cycles.FunctionFieldTransport
import all HodgeConjecture.Cycles.GradedFinitePushforward
import all HodgeConjecture.Cycles.GradedPushforward
import all HodgeConjecture.Cycles.HeightOneFiniteness
import all HodgeConjecture.Cycles.IdealComap
import all HodgeConjecture.Cycles.IdealStalk
import all HodgeConjecture.Cycles.IntegralCodimension
import all HodgeConjecture.Cycles.IntegralDimension
import all HodgeConjecture.Cycles.IsomorphismTransport
import all HodgeConjecture.Cycles.LocalOrder
import all HodgeConjecture.Cycles.LocalOrderDeterminant
import all HodgeConjecture.Cycles.LocalOrderLocalization
import all HodgeConjecture.Cycles.LocalOrderNorm
import all HodgeConjecture.Cycles.LocalOrderNormFormula
import all HodgeConjecture.Cycles.LocalOrderTransport
import all HodgeConjecture.Cycles.LocalizationTranscendenceDegree
import all HodgeConjecture.Cycles.NormalizationDimension
import all HodgeConjecture.Cycles.NormalizationLocalDimension
import all HodgeConjecture.Cycles.OpenClosedLocalization
import all HodgeConjecture.Cycles.OpenGrading
import all HodgeConjecture.Cycles.OpenRestriction
import all HodgeConjecture.Cycles.OpenSupport
import all HodgeConjecture.Cycles.PointSupport
import all HodgeConjecture.Cycles.PolynomialMaximalHeight
import all HodgeConjecture.Cycles.PolynomialPrimeHeight
import all HodgeConjecture.Cycles.PrincipalDivisor
import all HodgeConjecture.Cycles.PrincipalDivisorDegree
import all HodgeConjecture.Cycles.PrincipalDivisorImage
import all HodgeConjecture.Cycles.PrincipalDivisorTransport
import all HodgeConjecture.Cycles.PrincipalRelations
import all HodgeConjecture.Cycles.ProjectiveLineChow
import all HodgeConjecture.Cycles.ProjectiveLineCycleDegree
import all HodgeConjecture.Cycles.ProjectiveLineDivisorPoints
import all HodgeConjecture.Cycles.ProjectiveLineFunctionField
import all HodgeConjecture.Cycles.ProjectiveLineGlobalOrder
import all HodgeConjecture.Cycles.ProjectiveLineInversionOrder
import all HodgeConjecture.Cycles.ProjectiveLineOrderDictionary
import all HodgeConjecture.Cycles.ProjectiveLinePrincipalDegree
import all HodgeConjecture.Cycles.ProjectiveLinePrincipalDegreeZero
import all HodgeConjecture.Cycles.PullbackStalk
import all HodgeConjecture.Cycles.RationalChow
import all HodgeConjecture.Cycles.RationalFiniteChowPushforward
import all HodgeConjecture.Cycles.RationalFunctionPresentation
import all HodgeConjecture.Cycles.ResidueDegree
import all HodgeConjecture.Cycles.ResidueNormalizationLift
import all HodgeConjecture.Cycles.ResidueNormalizationLocalization
import all HodgeConjecture.Cycles.ScalarExtensionQuotient
import all HodgeConjecture.Cycles.SchemeLocalOrder
import all HodgeConjecture.Cycles.StalkBaseChange
import all HodgeConjecture.Cycles.StructuralResidueField
import all HodgeConjecture.Cycles.SupportCodimension
import all HodgeConjecture.Cycles.SupportDimension
import all HodgeConjecture.Cycles.TopDegreeRelations
import all HodgeConjecture.Cycles.TranscendenceDegreeDrop
import all HodgeConjecture.Geometry.AffineComplexPoints
import all HodgeConjecture.Geometry.ComplexPoints
import all HodgeConjecture.Geometry.ComplexPointsFunctoriality
import all HodgeConjecture.Geometry.ProjectiveLine
import all HodgeConjecture.Geometry.ProjectiveLineAffineChart
import all HodgeConjecture.Geometry.ProjectiveLineInfinityChart
import all HodgeConjecture.Geometry.ProjectiveLineOpenCover
import all HodgeConjecture.Geometry.ProjectiveLinePoints
import all HodgeConjecture.Geometry.ProjectiveLineProduct
import all HodgeConjecture.Geometry.ProjectiveLineProductSections
import all HodgeConjecture.Geometry.ProjectiveLineProperties
import all HodgeConjecture.Geometry.ProjectiveLineSquare
import all HodgeConjecture.Geometry.SectionAlgebra
import all HodgeConjecture.Inputs.FixedInertia
import all HodgeConjecture.LinearAlgebra.Harmonic.CellComplex
import all HodgeConjecture.LinearAlgebra.Harmonic.Cellular
import all HodgeConjecture.LinearAlgebra.Harmonic.Cohomology
import all HodgeConjecture.LinearAlgebra.Harmonic.Equivalence
import all HodgeConjecture.LinearAlgebra.Harmonic.Hodge
import all HodgeConjecture.LinearAlgebra.HomCoefficients
import all HodgeConjecture.LinearAlgebra.ModularRankCertificate
import all HodgeConjecture.LinearAlgebra.UniversalIdempotentAlgebra
import all HodgeConjecture.MathlibCompat.Automorphism
import all HodgeConjecture.MathlibCompat.DeclarationDependencies
import all HodgeConjecture.MathlibCompat.Ramification
import all HodgeConjecture.Realization.Betti.AffineSimplexChains
import all HodgeConjecture.Realization.Betti.BarycentricMesh
import all HodgeConjecture.Realization.Betti.ChainHomologyClasses
import all HodgeConjecture.Realization.Betti.Circle
import all HodgeConjecture.Realization.Betti.CircleCoverHarmonicComparison
import all HodgeConjecture.Realization.Betti.CochainDualComparison
import all HodgeConjecture.Realization.Betti.CochainDualCoordinates
import all HodgeConjecture.Realization.Betti.CochainPair
import all HodgeConjecture.Realization.Betti.CoverSingular
import all HodgeConjecture.Realization.Betti.CoverSmallChains
import all HodgeConjecture.Realization.Betti.CoverSubdivisionHomotopy
import all HodgeConjecture.Realization.Betti.CoverSubdivisionSmallness
import all HodgeConjecture.Realization.Betti.Examples.AffineLineComplexPoints
import all HodgeConjecture.Realization.Betti.Examples.CircleCohomology
import all HodgeConjecture.Realization.Betti.Examples.CircleInversion
import all HodgeConjecture.Realization.Betti.Examples.CircleOrientedCycle
import all HodgeConjecture.Realization.Betti.Examples.CircleOrientedPairing
import all HodgeConjecture.Realization.Betti.Examples.CircleSquare
import all HodgeConjecture.Realization.Betti.Examples.CircleTopology
import all HodgeConjecture.Realization.Betti.Examples.ComplexPointThom
import all HodgeConjecture.Realization.Betti.Examples.ComplexSquareThom
import all HodgeConjecture.Realization.Betti.Examples.OnePointComplexInversion
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineAffine
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineAnalyticCover
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineComplexPoints
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineFinitePointSupport
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineInfinitySupport
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineNormalChart
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineNormalChartBoundary
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLinePointSupport
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineReciprocal
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineSingularCohomology
import all HodgeConjecture.Realization.Betti.Examples.PuncturedComplexCircle
import all HodgeConjecture.Realization.Betti.NativeSimplexGeometry
import all HodgeConjecture.Realization.Betti.ProjectiveLineCohomology
import all HodgeConjecture.Realization.Betti.ProjectiveLineComplexification
import all HodgeConjecture.Realization.Betti.ProjectiveLineCoverHarmonicComparison
import all HodgeConjecture.Realization.Betti.ProjectiveLineCycleClass
import all HodgeConjecture.Realization.Betti.ProjectiveLineFinitePointGysin
import all HodgeConjecture.Realization.Betti.ProjectiveLineFiniteSupportGysin
import all HodgeConjecture.Realization.Betti.ProjectiveLineGysinCycleClass
import all HodgeConjecture.Realization.Betti.ProjectiveLineHodgeStructure
import all HodgeConjecture.Realization.Betti.ProjectiveLineInfinityGysin
import all HodgeConjecture.Realization.Betti.ProjectiveLineOrientation
import all HodgeConjecture.Realization.Betti.ProjectiveLinePointGysin
import all HodgeConjecture.Realization.Betti.ProjectiveLineProductClasses
import all HodgeConjecture.Realization.Betti.ProjectiveLineSquareGysin
import all HodgeConjecture.Realization.Betti.ProjectiveLineSquarePullback
import all HodgeConjecture.Realization.Betti.ProjectiveLineSquareRamification
import all HodgeConjecture.Realization.Betti.ProjectiveLineSupportedPoint
import all HodgeConjecture.Realization.Betti.RationalDual
import all HodgeConjecture.Realization.Betti.RelativeAdditivity
import all HodgeConjecture.Realization.Betti.RelativeCochains
import all HodgeConjecture.Realization.Betti.RelativeCochainsNaturality
import all HodgeConjecture.Realization.Betti.RelativeExcision
import all HodgeConjecture.Realization.Betti.RelativeMayerVietoris
import all HodgeConjecture.Realization.Betti.RelativeUnion
import all HodgeConjecture.Realization.Betti.RelativeUnionSplit
import all HodgeConjecture.Realization.Betti.Scheme
import all HodgeConjecture.Realization.Betti.ShortExactQuasiIso
import all HodgeConjecture.Realization.Betti.SimplicialCochains
import all HodgeConjecture.Realization.Betti.SingularChainCoordinates
import all HodgeConjecture.Realization.Betti.SingularCochains
import all HodgeConjecture.Realization.Betti.SingularComponents
import all HodgeConjecture.Realization.Betti.SingularContractible
import all HodgeConjecture.Realization.Betti.SingularCyclePairing
import all HodgeConjecture.Realization.Betti.SingularDegreeZero
import all HodgeConjecture.Realization.Betti.SingularDegreeZeroNaturality
import all HodgeConjecture.Realization.Betti.SingularFiniteSupport
import all HodgeConjecture.Realization.Betti.SingularHomotopy
import all HodgeConjecture.Realization.Betti.SingularMayerVietoris
import all HodgeConjecture.Realization.Betti.SingularMayerVietorisMaps
import all HodgeConjecture.Realization.Betti.SingularMayerVietorisNaturality
import all HodgeConjecture.Realization.Betti.SingularMayerVietorisSwap
import all HodgeConjecture.Realization.Betti.SingularPathConnected
import all HodgeConjecture.Realization.Betti.SingularSubcomplexes
import all HodgeConjecture.Realization.Betti.SingularSubdivision
import all HodgeConjecture.Realization.Betti.SingularSubdivisionHomology
import all HodgeConjecture.Realization.Betti.SingularSubdivisionHomotopy
import all HodgeConjecture.Realization.Betti.SingularSubdivisionIteration
import all HodgeConjecture.Realization.Betti.SingularSubdivisionLocality
import all HodgeConjecture.Realization.Betti.SingularSubdivisionSmallness
import all HodgeConjecture.Realization.Betti.SingularSupportedChains
import all HodgeConjecture.Realization.Betti.SingularSupports
import all HodgeConjecture.Realization.Betti.SmallSingularComparison
import all HodgeConjecture.Realization.Betti.SmallSingularSubdivisionHomotopy
import all HodgeConjecture.Realization.Betti.SubcomplexChainCoordinates
import all HodgeConjecture.Realization.Betti.SubcomplexCochains
import all HodgeConjecture.Realization.Betti.SubcomplexConnectingRepresentative
import all HodgeConjecture.Realization.Betti.SubcomplexDegreeZeroRepresentative
import all HodgeConjecture.Realization.Betti.SubcomplexOperators
import all HodgeConjecture.Realization.Betti.SubdivisionGeometry
import all HodgeConjecture.Realization.Betti.TwoComponentBoundary
import all HodgeConjecture.Realization.Betti.VertexSubdivision
import all HodgeConjecture.Realization.Betti.VertexSubdivisionLocality
import all HodgeConjecture.Realization.Betti.VertexSubdivisionNaturality
import all HodgeConjecture.Realization.Chow.FiniteCoverCoverage
import all HodgeConjecture.Realization.Chow.FiniteCoverageCertificate
import all HodgeConjecture.Realization.Chow.HarmonicWitness
import all HodgeConjecture.Realization.Chow.Model
import all HodgeConjecture.Realization.Chow.ProjectiveLineFinitePoint
import all HodgeConjecture.Realization.Chow.ProjectiveLineSquare
import all HodgeConjecture.Realization.Chow.ProjectiveLineSquareRamification
import all HodgeConjecture.Realization.Chow.TransferProjector
import all HodgeConjecture.Realization.Chow.UpstairsGeneration
import all HodgeConjecture.Realization.DeRham.AffineCohomology
import all HodgeConjecture.Realization.DeRham.AffineDegreeZero
import all HodgeConjecture.Realization.DeRham.AffineFormsSheaf
import all HodgeConjecture.Realization.DeRham.AffineSectionCoordinates
import all HodgeConjecture.Realization.DeRham.AffineSheafAcyclicity
import all HodgeConjecture.Realization.DeRham.BettiHodgeTarget
import all HodgeConjecture.Realization.DeRham.DegreeFiltration
import all HodgeConjecture.Realization.DeRham.HypercohomologyFiltration
import all HodgeConjecture.Realization.DeRham.LaurentDifferentials
import all HodgeConjecture.Realization.DeRham.LaurentFormsSheaf
import all HodgeConjecture.Realization.DeRham.LaurentLogarithmicRegulator
import all HodgeConjecture.Realization.DeRham.LaurentOrientedArcs
import all HodgeConjecture.Realization.DeRham.LaurentPeriods
import all HodgeConjecture.Realization.DeRham.LaurentProjectiveCharts
import all HodgeConjecture.Realization.DeRham.LaurentResidue
import all HodgeConjecture.Realization.DeRham.Logarithmic
import all HodgeConjecture.Realization.DeRham.OpenImmersionForms
import all HodgeConjecture.Realization.DeRham.OpenImmersionTrivialization
import all HodgeConjecture.Realization.DeRham.PresheafComplex
import all HodgeConjecture.Realization.DeRham.ProjectiveLineCech
import all HodgeConjecture.Realization.DeRham.ProjectiveLineCechReduction
import all HodgeConjecture.Realization.DeRham.ProjectiveLineChern
import all HodgeConjecture.Realization.DeRham.ProjectiveLineCohomology
import all HodgeConjecture.Realization.DeRham.ProjectiveLineCoverageCertificate
import all HodgeConjecture.Realization.DeRham.ProjectiveLineCycleClass
import all HodgeConjecture.Realization.DeRham.ProjectiveLineFinitePointComparison
import all HodgeConjecture.Realization.DeRham.ProjectiveLineFiniteSupportComparison
import all HodgeConjecture.Realization.DeRham.ProjectiveLineFormsSheaf
import all HodgeConjecture.Realization.DeRham.ProjectiveLineHigherSheaves
import all HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeComparison
import all HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeCycleClass
import all HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeFiltration
import all HodgeConjecture.Realization.DeRham.ProjectiveLinePeriodComparison
import all HodgeConjecture.Realization.DeRham.ProjectiveLinePeriods
import all HodgeConjecture.Realization.DeRham.ProjectiveLinePointGysinComparison
import all HodgeConjecture.Realization.DeRham.ProjectiveLineRamificationComparison
import all HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeCharts
import all HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeComparison
import all HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeCycleClass
import all HodgeConjecture.Realization.DeRham.ProjectiveLineSheafAcyclicity
import all HodgeConjecture.Realization.DeRham.ProjectiveLineSheafCech
import all HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage
import all HodgeConjecture.Realization.DeRham.SchemeHodgeFiltration
import all HodgeConjecture.Realization.DeRham.SheafComplex
import all HodgeConjecture.Realization.DeRham.SheafHypercohomology
import all HodgeConjecture.Realization.DeRham.TwoTermDegreeFiltration
import all HodgeConjecture.Realization.DeRham.TwoTermHypercohomology
import all HodgeConjecture.Realization.FilteredHodgeTarget
import all HodgeConjecture.Realization.HodgeClasses
import all HodgeConjecture.Realization.HodgeFiltration
import all HodgeConjecture.Realization.Transfer
import all HodgeConjecture.SheafCohomology.AffineCoefficients
import all HodgeConjecture.SheafCohomology.AffineVanishing
import all HodgeConjecture.SheafCohomology.Basis
import all HodgeConjecture.SheafCohomology.BasisDegreeOne
import all HodgeConjecture.SheafCohomology.CechComplex
import all HodgeConjecture.SheafCohomology.DerivedPostcompose
import all HodgeConjecture.SheafCohomology.FlasqueCechVanishing
import all HodgeConjecture.SheafCohomology.FlasqueDerived
import all HodgeConjecture.SheafCohomology.Hypercohomology
import all HodgeConjecture.SheafCohomology.InjectiveRestriction
import all HodgeConjecture.SheafCohomology.LinearCoefficients
import all HodgeConjecture.SheafCohomology.LinearRestriction
import all HodgeConjecture.SheafCohomology.LinearSheaves
import all HodgeConjecture.SheafCohomology.LocalAffineCoefficients
import all HodgeConjecture.SheafCohomology.Locality
import all HodgeConjecture.SheafCohomology.OpenImmersionRestriction
import all HodgeConjecture.SheafCohomology.QuasicoherentBaseChange
import all HodgeConjecture.SheafCohomology.RingCechAcyclicity
import all HodgeConjecture.SheafCohomology.StandardCoverVanishing
import all HodgeConjecture.SheafCohomology.StandardOpenCover
import all HodgeConjecture.SheafCohomology.StructureModule
import all HodgeConjecture.SheafCohomology.TwoOpenModules
import all HodgeConjecture.Topology.OnePointHomotopy
-- END GENERATED PROJECT PRIVATE IMPORTS

@[expose] public section

/-! Actual finite-support H⁰ and relative assembly retain all original pair
maps. In particular the two-point balanced class is nonzero before support
forgetting and zero afterward. Weighted original cycles and the unchanged
full-target certificate are checked separately. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification

open AlgebraicGeometry CategoryTheory HomologicalComplex Opposite Simplicial SchemeCycles
open ProjectiveLineComplexPoints ProjectiveLineBettiCohomology
open ProjectiveLineFiniteSupportComparison
open scoped BigOperators

local instance : DecidableEq Point := Classical.decEq Point

def twoPoints : Finset Point := {finite 0, infinity}
def zeroPoint : Support twoPoints := ⟨finite 0, by simp [twoPoints]⟩
def infinityPoint : Support twoPoints := ⟨infinity, by simp [twoPoints]⟩

private theorem twoPoints_card : twoPoints.card = 2 := by
  simp [twoPoints, finite_ne_infinity 0]

lemma twoPoints_nonempty : twoPoints.Nonempty :=
  ⟨finite 0, by simp [twoPoints]⟩

private theorem zeroPoint_ne_infinityPoint : zeroPoint ≠ infinityPoint := by
  intro h
  exact finite_ne_infinity 0 (congrArg Subtype.val h)

def balancedSource : H0 twoPoints :=
  SingularFiniteSupport.deltaClass twoPoints zeroPoint -
    SingularFiniteSupport.deltaClass twoPoints infinityPoint

private theorem average_coordinate (S : Finset Point) (hS : S.Nonempty) :
    h2Equiv (model.cycleClass (averageClass S)) = 1 := by
  rw [averageClass_cycleClass S hS, h2Equiv_coverGenerator]

theorem unchanged_model_basis_source_and_original_maps :
    model = ProjectiveLineCoverageCertificate.model ∧
    basis = ProjectiveLineCoverageCertificate.basis ∧
    CoverChow = RationalChowGroup
      (DimensionFunction.ofLocallyOfFiniteType ℂ (projectiveLine ℂ)
        (cover ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)))) 0 ∧
    actualPull = rationalChowFiniteFlatPullback ℂ
      (projectiveLine ℂ ↘ Spec (.of ℂ)) cover 0 ∧
    actualPush = rationalChowFinitePushforward ℂ
      (projectiveLine ℂ ↘ Spec (.of ℂ)) cover 0 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem actual_h0_source_and_original_point_evaluation
    (S : Finset Point) (z : H0 S) (p : Support S) :
    H0 S = SingularCochains.Cohomology (TopCat.of ↥(S : Set Point)) 0 ∧
    SingularFiniteSupport.coordinates S z p = SingularDegreeZero.eval (Support S)
      ((SingularCochains.cohomologyZeroIso (Support S)).hom z) p :=
  ⟨rfl, SingularFiniteSupport.coordinates_apply S z p⟩

theorem singleton_restriction_is_actual_pullback_and_evaluation
    (S : Finset Point) (z : H0 S) (p : Support S) :
    SingularFiniteSupport.pointRestriction S p =
      (SingularCochains.cohomologyPullback
        (TopCat.ofHom (SingularFiniteSupport.singletonInclusion S p)) 0).hom ∧
    SingularFiniteSupport.pointCoordinates p.val
        (SingularFiniteSupport.pointRestriction S p z) = SingularFiniteSupport.coordinates S z p :=
  ⟨rfl, SingularFiniteSupport.pointCoordinates_pointRestriction S p z⟩

theorem actual_delta_classes_restrict_to_the_same_singleton_units
    (S : Finset Point) (p q : Support S) (hpq : p ≠ q) :
    SingularFiniteSupport.coordinates S (SingularFiniteSupport.deltaClass S p) p = 1 ∧
    SingularFiniteSupport.coordinates S (SingularFiniteSupport.deltaClass S p) q = 0 ∧
    SingularFiniteSupport.pointRestriction S p (SingularFiniteSupport.deltaClass S p) =
      SingularFiniteSupport.pointUnit p.val ∧
    SingularFiniteSupport.pointRestriction S q (SingularFiniteSupport.deltaClass S p) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (SingularFiniteSupport.coordinates_deltaClass S p p).trans (ite_eq_left rfl)
  · exact (SingularFiniteSupport.coordinates_deltaClass S p q).trans (ite_eq_right hpq)
  · exact (SingularFiniteSupport.pointRestriction_deltaClass S p p).trans (ite_eq_left rfl)
  · exact (SingularFiniteSupport.pointRestriction_deltaClass S q p).trans (ite_eq_right hpq)

theorem point_deltas_reconstruct_original_h0_and_constant_mass
    (S : Finset Point) (z : H0 S) (q : ℚ) :
    (∑ p : Support S, SingularFiniteSupport.coordinates S z p •
      SingularFiniteSupport.deltaClass S p) = z ∧
    SingularFiniteSupport.sumCoordinates S
      (SingularDegreeZeroNaturality.constantClass (Support S) q) = (S.card : ℚ) * q :=
  ⟨SingularFiniteSupport.sum_coordinates_deltaClass S z,
    SingularFiniteSupport.sumCoordinates_constantClass S q⟩

theorem empty_support_has_zero_original_source_and_relative_target
    (n : ℕ) (z : H0 (∅ : Finset Point))
    (w : SingularSupports.Supported Point ∅ n) :
    z = 0 ∧ w = 0 ∧ ProjectiveLineFiniteSupportGysin.supportedGysin ∅ z = 0 :=
  ⟨SingularFiniteSupport.empty_eq_zero z, SingularSupports.empty_eq_zero Point n w,
    ProjectiveLineFiniteSupportGysin.empty_supportedGysin z⟩

theorem relative_union_split_retains_actual_compatible_function_gluing
    {T : SSet.{0}} (A B : T.Subcomplex) (n : ℕ)
    (φ : RelativeCochains.Cochain (RelativeUnionSplit.leftBoundary A B) n ×
      RelativeCochains.Cochain (RelativeUnionSplit.rightBoundary A B) n) :
    ((RelativeUnionSplit.cochainEquiv A B n).symm φ).val =
      SubcomplexCochains.glueFunction A B n (φ.1.val, φ.2.val) ∧
    SubcomplexCochains.coverRestrictionLinear A B n
      (RelativeUnionSplit.glueFunction A B n φ) = (φ.1.val, φ.2.val) :=
  ⟨RelativeUnionSplit.cochainEquiv_symm_val A B n φ,
    RelativeUnionSplit.glueFunction_restrictions A B n φ⟩

theorem all_degree_support_extensions_are_original_composable_pair_maps
    (F G H : Set Point) (hFG : F ⊆ G) (hGH : G ⊆ H) (n : ℕ) :
    SingularSupports.extensionComplex Point hFG = RelativeCochains.pullback
      (𝟙 (SingularSupports.singular Point)) (SingularSupports.extensionCondition Point hFG) ∧
    SingularSupports.extensionComplex Point hFG ≫ SingularSupports.extensionComplex Point hGH =
      SingularSupports.extensionComplex Point (hFG.trans hGH) ∧
    (SingularSupports.extension Point hGH n).comp (SingularSupports.extension Point hFG n) =
      SingularSupports.extension Point (hFG.trans hGH) n ∧
    (SingularSupports.forget Point G n).comp (SingularSupports.extension Point hFG n) =
      SingularSupports.forget Point F n :=
  ⟨rfl, SingularSupports.extensionComplex_trans Point hFG hGH,
    SingularSupports.extension_trans Point hFG hGH n,
    SingularSupports.extension_forget Point hFG n⟩

theorem canonical_assembly_is_the_same_actual_bijection_in_every_degree
    (S : Finset Point) (n : ℕ) (φ : SingularSupports.Family Point S n) :
    (SingularSupports.assembleIso Point S n).hom.hom = SingularSupports.assemble Point S n ∧
    SingularSupports.assemble Point S n φ =
      (∑ p : Support S, SingularSupports.singletonExtension Point S p n (φ p)) ∧
    Function.Bijective (SingularSupports.assemble Point S n) :=
  ⟨SingularSupports.assembleIso_hom Point S n,
    SingularSupports.assemble_apply Point S n φ, SingularSupports.assemble_bijective Point S n⟩

theorem finite_gysin_components_are_original_point_restrictions_and_thom_maps
    (S : Finset Point) (z : H0 S) (p : Support S) :
    ProjectiveLineFiniteSupportGysin.pointRestrictionsEquiv S z p =
        SingularFiniteSupport.pointRestriction S p z ∧
    ProjectiveLineFiniteSupportGysin.componentMap S z p =
      ProjectiveLineSupportedPoint.supportedGysin p.val
        (SingularFiniteSupport.pointRestriction S p z) :=
  ⟨ProjectiveLineFiniteSupportGysin.pointRestrictionsEquiv_apply S z p, rfl⟩

theorem finite_gysin_is_an_iso_of_the_original_supported_target
    (S : Finset Point) (z : H0 S) :
    ProjectiveLineFiniteSupportGysin.SupportedH2 S =
      RelativeCochains.Cohomology (SingularSupports.boundary Point (S : Set Point)) 2 ∧
    ProjectiveLineFiniteSupportGysin.gysinEquiv S z =
      ProjectiveLineFiniteSupportGysin.supportedGysin S z ∧
    Function.Bijective (ProjectiveLineFiniteSupportGysin.supportedGysin S) :=
  ⟨rfl, ProjectiveLineFiniteSupportGysin.gysinEquiv_apply S z,
    ProjectiveLineFiniteSupportGysin.supportedGysin_bijective S⟩

theorem point_delta_gysin_is_actual_singleton_support_extension
    (S : Finset Point) (p : Support S) :
    ProjectiveLineFiniteSupportGysin.supportedGysin S (SingularFiniteSupport.deltaClass S p) =
      SingularSupports.singletonExtension Point S p 2
        (ProjectiveLineSupportedPoint.supportedGysin p.val (SingularFiniteSupport.pointUnit p.val)) :=
  ProjectiveLineFiniteSupportGysin.supportedGysin_deltaClass S p

theorem point_isomorphisms_use_original_finite_and_reciprocal_normal_charts (a : ℂ) :
    ProjectiveLineSupportedPoint.isoOfChart (ProjectiveLineSupportedPoint.Chart.finite a) =
      ProjectiveLineFinitePointGysin.pointPullbackIso a ≪≫ ComplexPointThom.thomIso.toModuleIso ≪≫
        ProjectiveLineFinitePointGysin.thomToSupportIso a 1 ∧
    ProjectiveLineSupportedPoint.isoOfChart ProjectiveLineSupportedPoint.Chart.infinity =
      ProjectiveLineInfinityGysin.pointPullbackIso ≪≫ ComplexPointThom.thomIso.toModuleIso ≪≫
        ProjectiveLineInfinityGysin.thomToSupportIso 1 ≪≫ ProjectiveLineSupportedPoint.infinitySupportIso :=
  ⟨rfl, rfl⟩

theorem two_point_control_uses_actual_zero_and_infinity :
    twoPoints.card = 2 ∧ zeroPoint.val = finite 0 ∧ infinityPoint.val = infinity ∧
    zeroPoint ≠ infinityPoint ∧ twoPoints.Nonempty :=
  ⟨twoPoints_card, rfl, rfl, zeroPoint_ne_infinityPoint, twoPoints_nonempty⟩

theorem balanced_original_h0_is_nonzero_with_zero_actual_mass :
    SingularFiniteSupport.coordinates twoPoints balancedSource zeroPoint = 1 ∧
    SingularFiniteSupport.coordinates twoPoints balancedSource infinityPoint = -1 ∧
    SingularFiniteSupport.sumCoordinates twoPoints balancedSource = 0 ∧ balancedSource ≠ 0 := by
  refine ⟨?_, ?_, ?_, ProjectiveLineFiniteSupportGysin.delta_difference_ne_zero
    twoPoints zeroPoint infinityPoint zeroPoint_ne_infinityPoint⟩
  · have h := congrFun ((SingularFiniteSupport.coordinates twoPoints).map_sub
      (SingularFiniteSupport.deltaClass twoPoints zeroPoint)
      (SingularFiniteSupport.deltaClass twoPoints infinityPoint)) zeroPoint
    change SingularFiniteSupport.coordinates twoPoints balancedSource zeroPoint =
      SingularFiniteSupport.coordinates twoPoints (SingularFiniteSupport.deltaClass twoPoints zeroPoint) zeroPoint -
        SingularFiniteSupport.coordinates twoPoints (SingularFiniteSupport.deltaClass twoPoints infinityPoint) zeroPoint at h
    rw [show SingularFiniteSupport.coordinates twoPoints
        (SingularFiniteSupport.deltaClass twoPoints zeroPoint) zeroPoint = 1 from
          (SingularFiniteSupport.coordinates_deltaClass twoPoints zeroPoint zeroPoint).trans (ite_eq_left rfl),
      show SingularFiniteSupport.coordinates twoPoints
        (SingularFiniteSupport.deltaClass twoPoints infinityPoint) zeroPoint = 0 from
          (SingularFiniteSupport.coordinates_deltaClass twoPoints infinityPoint zeroPoint).trans
            (ite_eq_right (Ne.symm zeroPoint_ne_infinityPoint)), sub_zero] at h
    exact h
  · have h := congrFun ((SingularFiniteSupport.coordinates twoPoints).map_sub
      (SingularFiniteSupport.deltaClass twoPoints zeroPoint)
      (SingularFiniteSupport.deltaClass twoPoints infinityPoint)) infinityPoint
    change SingularFiniteSupport.coordinates twoPoints balancedSource infinityPoint =
      SingularFiniteSupport.coordinates twoPoints (SingularFiniteSupport.deltaClass twoPoints zeroPoint) infinityPoint -
        SingularFiniteSupport.coordinates twoPoints (SingularFiniteSupport.deltaClass twoPoints infinityPoint) infinityPoint at h
    rw [show SingularFiniteSupport.coordinates twoPoints
        (SingularFiniteSupport.deltaClass twoPoints zeroPoint) infinityPoint = 0 from
          (SingularFiniteSupport.coordinates_deltaClass twoPoints zeroPoint infinityPoint).trans
            (ite_eq_right zeroPoint_ne_infinityPoint),
      show SingularFiniteSupport.coordinates twoPoints
        (SingularFiniteSupport.deltaClass twoPoints infinityPoint) infinityPoint = 1 from
          (SingularFiniteSupport.coordinates_deltaClass twoPoints infinityPoint infinityPoint).trans (ite_eq_left rfl),
      zero_sub] at h
    exact h
  · rw [balancedSource, map_sub, SingularFiniteSupport.sumCoordinates_deltaClass,
      SingularFiniteSupport.sumCoordinates_deltaClass, sub_self]

theorem balanced_gysin_is_nonzero_in_original_supported_cohomology :
    ProjectiveLineFiniteSupportGysin.supportedGysin twoPoints balancedSource ≠ 0 :=
  ProjectiveLineFiniteSupportGysin.supported_difference_ne_zero
    twoPoints zeroPoint infinityPoint zeroPoint_ne_infinityPoint

theorem balanced_support_forgetting_is_zero_and_is_not_injective :
    SingularSupports.forget Point (twoPoints : Set Point) 2
        (ProjectiveLineFiniteSupportGysin.supportedGysin twoPoints balancedSource) = 0 ∧
    ¬ Function.Injective (SingularSupports.forget Point (twoPoints : Set Point) 2) :=
  ⟨ProjectiveLineFiniteSupportGysin.forget_difference_zero twoPoints zeroPoint infinityPoint,
    ProjectiveLineFiniteSupportGysin.forget_not_injective
      twoPoints zeroPoint infinityPoint zeroPoint_ne_infinityPoint⟩

theorem weighted_cycle_source_is_the_original_representative_and_ordinary_quotient
    (S : Finset Point) (z : H0 S) (p : Point) :
    ProjectiveLineFiniteSupportComparison.Cycle = cyclesOfDegree ℚ (ProjectiveLineCycles.dimensionFunction ℂ) 0 ∧
    pointRepresentative p = ProjectiveLineCycles.pointCycle ℂ ℚ
      (schemeMorphism p (default : Spec (.of ℂ))) (schemePoint_ne_genericPoint p) ∧
    classMap S z = rationalClassMap (ProjectiveLineCycles.dimensionFunction ℂ) 0 (cycle S z) :=
  ⟨rfl, rfl, rfl⟩

theorem raw_cycle_and_quotient_use_the_same_actual_point_coefficients
    (S : Finset Point) (z : H0 S) :
    cycle S z = (∑ p : Support S, SingularFiniteSupport.coordinates S z p • pointRepresentative p.val) ∧
    classMap S z = (∑ p : Support S, SingularFiniteSupport.coordinates S z p • pointClass p.val) :=
  ⟨cycle_apply S z, classMap_apply S z⟩

theorem original_supported_gysin_forgetting_matches_original_weighted_cycle_class
    (S : Finset Point) (z : H0 S) :
    SingularSupports.forget Point (S : Set Point) 2
        (ProjectiveLineFiniteSupportGysin.gysinEquiv S z) = model.cycleClass (classMap S z) ∧
    ProjectiveLineFiniteSupportGysin.gysin S z =
      SingularFiniteSupport.sumCoordinates S z • coverGenerator ∧
    model.cycleClass (classMap S z) = SingularFiniteSupport.sumCoordinates S z • coverGenerator :=
  ⟨supported_cycleClass_comparison S z, ProjectiveLineFiniteSupportGysin.gysin_apply S z,
    classMap_cycleClass S z⟩

theorem average_is_the_same_raw_cycle_before_the_original_quotient (S : Finset Point) :
    averageCycle S = (S.card : ℚ)⁻¹ • cycle S (supportUnit S) ∧
    averageClass S = rationalClassMap (ProjectiveLineCycles.dimensionFunction ℂ) 0 (averageCycle S) ∧
    averageClass S = (S.card : ℚ)⁻¹ • classMap S (supportUnit S) :=
  ⟨rfl, rfl, averageClass_eq S⟩

theorem nonempty_support_mass_and_average_supply_original_full_target
    (S : Finset Point) (hS : S.Nonempty) :
    SingularFiniteSupport.sumCoordinates S (supportUnit S) = (S.card : ℚ) ∧
    (S.card : ℚ) ≠ 0 ∧ model.cycleClass (averageClass S) = coverGenerator :=
  ⟨mass_supportUnit S, card_ne_zero S hS, averageClass_cycleClass S hS⟩

theorem actual_global_degree_is_rank_at_a_selected_actual_support_point
    (S : Finset Point) (hS : S.Nonempty) :
    selectedPoint S hS ∈ S ∧
    (transfer S hS).degree = cover.finrank (schemePoint (selectedPoint S hS)) ∧
    (transfer S hS).degree = 2 ∧
    ∀ x : scheme, (transfer S hS).degree = cover.finrank x :=
  ⟨selectedPoint_mem S hS, rfl, degree_eq_two S hS, degree_eq_geometric_rank S hS⟩

theorem every_nonempty_finite_support_has_same_full_model_certificate
    (S : Finset Point) (hS : S.Nonempty) :
    FiniteCoverageCertificate.check (certificate S hS) = true ∧
    (certificate S hS).cycles () = averageClass S ∧
    RationalHodgeConjectureAt ProjectiveLineCoverageCertificate.model :=
  ⟨accepted S hS, normalized_cycles S hS (), model_satisfies_from_nonempty_finite_support S hS⟩

theorem concrete_two_point_normalization_uses_actual_cardinality_two :
    SingularFiniteSupport.sumCoordinates twoPoints (supportUnit twoPoints) = 2 ∧
    averageClass twoPoints = (2 : ℚ)⁻¹ • classMap twoPoints (supportUnit twoPoints) ∧
    (certificate twoPoints twoPoints_nonempty).cycles () = averageClass twoPoints := by
  refine ⟨?_, ?_, normalized_cycles twoPoints twoPoints_nonempty ()⟩
  · simpa only [twoPoints_card, Nat.cast_ofNat] using mass_supportUnit twoPoints
  · simpa only [twoPoints_card, Nat.cast_ofNat] using averageClass_eq twoPoints

theorem empty_and_zero_mass_classes_cannot_supply_the_full_target
    (S : Finset Point) (z : H0 S) (hz : SingularFiniteSupport.sumCoordinates S z = 0) :
    averageClass ∅ = 0 ∧ model.cycleClass (averageClass ∅) ≠ coverGenerator ∧
    model.cycleClass (classMap S z) ≠ coverGenerator ∧
    model.cycleClass (classMap twoPoints balancedSource) ≠ coverGenerator := by
  refine ⟨averageClass_empty, empty_does_not_supply_target,
    zero_mass_does_not_supply_target S z hz, zero_mass_does_not_supply_target twoPoints balancedSource ?_⟩
  rw [balancedSource, map_sub, SingularFiniteSupport.sumCoordinates_deltaClass,
    SingularFiniteSupport.sumCoordinates_deltaClass, sub_self]

theorem unnormalized_push_fails_original_full_target_column
    (S : Finset Point) (hS : S.Nonempty) :
    model.cycleClass (actualPush (upstairsCycles S ())) ≠
      (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i ()) : Betti) := by
  intro h
  have hc := congrArg h2Equiv h
  change h2Equiv (model.cycleClass (actualPush (actualPull (averageClass S)))) = _ at hc
  rw [geometric_chow_push_pull S hS, map_smul, map_smul, average_coordinate S hS,
    degree_eq_two, target_column, h2Equiv_coverGenerator] at hc
  norm_num at hc

theorem degree_one_fails_and_normalization_recovers_original_average
    (S : Finset Point) (hS : S.Nonempty) :
    (¬ ∀ z : Betti, (transfer S hS).push ((transfer S hS).pull z) = (1 : ℚ) • z) ∧
    (((transfer S hS).degree : ℚ)⁻¹ • actualPush (actualPull (averageClass S)) = averageClass S) := by
  constructor
  · intro h
    have htwo : (transfer S hS).push ((transfer S hS).pull (model.cycleClass (averageClass S))) =
        ((transfer S hS).degree : ℚ) • model.cycleClass (averageClass S) := by
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (transfer S hS).push_comp_pull (model.cycleClass (averageClass S))
    have hc := congrArg h2Equiv (h (model.cycleClass (averageClass S)))
    rw [htwo, one_smul, map_smul, average_coordinate S hS, degree_eq_two] at hc
    norm_num at hc
  · rw [geometric_chow_push_pull S hS, smul_smul, degree_eq_two]
    norm_num

meta section

private def isProjectModule (name : Lean.Name) : Bool :=
  name == `HodgeConjecture || (`HodgeConjecture).isPrefixOf name

/-- Check every upstream import edge, including private modules omitted by the
current environment. Base `.olean` metadata preserves original import headers;
only missing/unloaded upstream headers are read, never their private bodies.
Returned regions stay retained; this audit never explicitly frees mappings. -/
private partial def checkUpstreamImports (env : Lean.Environment)
    (pending : List Lean.Name) (seen : Lean.NameSet)
    (regions : Array Lean.CompactedRegion) :
    IO (Lean.NameSet × Array Lean.CompactedRegion) := do
  match pending with
  | [] => pure (seen, regions)
  | name :: rest =>
    if seen.contains name then checkUpstreamImports env rest seen regions
    else
      if isProjectModule name then
        throw <| IO.userError s!"Project module {name} entered upstream import closure"
      let readHeader := do
        let (data, region) ← Lean.readModuleData (← Lean.findOLean name)
        pure (data, regions.push region)
      let (data, regions) ← match env.getModuleIdx? name with
        | some idx =>
            if env.header.modules[idx]!.hasData then
              pure (env.header.moduleData[idx]!, regions)
            else readHeader
        | none => readHeader
      let dependencies := data.imports.toList.map (·.module)
      for dependency in dependencies do
        if isProjectModule dependency then
          throw <| IO.userError s!"Upstream module {name} imports project module {dependency}"
      checkUpstreamImports env (dependencies ++ rest) (seen.insert name) regions

/-- The exact project-origin projection of checked declaration dependencies.
All project private bodies are required below. Every omitted upstream origin
is checked to have no project imports, so no path through it can return here. -/
private partial def visitProjectDeclarations (env : Lean.Environment)
    (pending : List Lean.Name) (seen : Lean.NameSet) : Except String Lean.NameSet :=
  match pending with
  | [] => .ok seen
  | name :: rest =>
    if seen.contains name then visitProjectDeclarations env rest seen
    else do
      let isProject := match env.getModuleIdxFor? name with
        | some idx => isProjectModule env.header.modules[idx]!.module
        | none => false
      let inspectBody := isProject || (env.getModuleIdxFor? name).isNone
      let dependencies ←
        if inspectBody then do
          let info ← match env.checked.get.find? name with
            | some info => pure info
            | none => throw s!"Missing checked project/local declaration {name}"
          if isProject && info.isAxiom then
            throw s!"Project declaration {name} is an axiom or has an erased body"
          let typeDependencies := info.type.getUsedConstants.toList
          if info.hasValue (allowOpaque := true) then
            let value ← match info.value? (allowOpaque := true) with
              | some value => pure value
              | none => throw s!"Missing checked definition/theorem body for {name}"
            pure (typeDependencies ++ value.getUsedConstants.toList)
          else
            match info with
            | .inductInfo inductiveInfo => pure (typeDependencies ++ inductiveInfo.ctors)
            | _ => pure typeDependencies
        else pure []
      visitProjectDeclarations env (dependencies ++ rest) (seen.insert name)

private def projectDependencies (env : Lean.Environment)
    (endpoint : Lean.Name) : Except String Lean.NameSet :=
  visitProjectDeclarations (env.setExporting false) [endpoint] {}

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.isModule do
    throwError "Project dependency audit must use Lean module mode"
  unless env.header.moduleData.size = env.header.modules.size do
    throwError "Imported module data and origin indices are misaligned"
  let mut projectCount : Nat := 0
  for idx in [:env.header.modules.size] do
    let effective := env.header.modules[idx]!
    if isProjectModule effective.module then
      projectCount := projectCount + 1
      unless effective.importAll && effective.hasData do
        throwError "Project private bodies not fully imported for {effective.module}"
  unless projectCount > 0 do
    throwError "No project modules were checked for private-body coverage"
  let upstream := env.header.modules.toList.filterMap fun effective ↦
    if isProjectModule effective.module then none else some effective.module
  let (checkedUpstream, metadataRegions) ← liftIO (checkUpstreamImports env upstream {} #[])
  logInfo m!"PASS complete project-body visibility and upstream boundary: {projectCount} project modules; {checkedUpstream.toList.length} upstream metadata nodes; {metadataRegions.size} additional exported headers"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.RelativeUnionSplit.cochainEquiv,
    `HodgeConjecture.RelativeUnionSplit.cochainEquiv_symm_val,
    `HodgeConjecture.RelativeUnionSplit.complexIso,
    `HodgeConjecture.RelativeUnionSplit.cohomologyEquiv,
    `HodgeConjecture.RelativeUnionSplit.toUnion_quasiIso,
    `HodgeConjecture.RelativeAdditivity.extension_trans,
    `HodgeConjecture.RelativeAdditivity.extension_forget,
    `HodgeConjecture.RelativeAdditivity.sumEquiv_apply,
    `HodgeConjecture.RelativeAdditivity.sumMap_bijective,
    `HodgeConjecture.SingularFiniteSupport.coordinates_apply,
    `HodgeConjecture.SingularFiniteSupport.coordinates_constantClass,
    `HodgeConjecture.SingularFiniteSupport.coordinates_deltaClass,
    `HodgeConjecture.SingularFiniteSupport.sum_coordinates_deltaClass,
    `HodgeConjecture.SingularFiniteSupport.pointRestriction,
    `HodgeConjecture.SingularFiniteSupport.pointCoordinates_pointRestriction,
    `HodgeConjecture.SingularFiniteSupport.pointRestriction_deltaClass,
    `HodgeConjecture.SingularFiniteSupport.sumCoordinates_constantClass,
    `HodgeConjecture.SingularFiniteSupport.sumCoordinates_deltaClass,
    `HodgeConjecture.SingularFiniteSupport.empty_eq_zero,
    `HodgeConjecture.SingularSupports.extensionComplex_trans,
    `HodgeConjecture.SingularSupports.extension_forget,
    `HodgeConjecture.SingularSupports.empty_eq_zero,
    `HodgeConjecture.SingularSupports.assemble_apply,
    `HodgeConjecture.SingularSupports.forget_assemble,
    `HodgeConjecture.SingularSupports.assemble_insert,
    `HodgeConjecture.SingularSupports.relativeBinary_bijective_of_eq,
    `HodgeConjecture.SingularSupports.insertBinaryMap_bijective,
    `HodgeConjecture.SingularSupports.assemble_bijective,
    `HodgeConjecture.SingularSupports.assembleEquiv_toLinearMap,
    `HodgeConjecture.ProjectiveLineSupportedPoint.isoOfChart,
    `HodgeConjecture.ProjectiveLineSupportedPoint.infinityCochainIso,
    `HodgeConjecture.ProjectiveLineSupportedPoint.gysinIso,
    `HodgeConjecture.ProjectiveLineSupportedPoint.supportedGysin_bijective,
    `HodgeConjecture.ProjectiveLineSupportedPoint.forget_isoOfChart_unit,
    `HodgeConjecture.ProjectiveLineSupportedPoint.gysin_pointUnit,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.pointRestrictionsEquiv_apply,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.componentMap,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.supportedGysin,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.gysinEquiv_apply,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.supportedGysin_bijective,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.gysin_apply,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.supportedGysin_deltaClass,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.delta_difference_ne_zero,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.supported_difference_ne_zero,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.forget_difference_zero,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.forget_not_injective,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.empty_supportedGysin,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.pointRepresentative,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.cycle_apply,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.classMap_apply,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.pointGysin_unit_cycleClass,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.supported_cycleClass_comparison,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.classMap_cycleClass,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.supportUnit,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.mass_supportUnit,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.averageClass_eq,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.averageClass_cycleClass,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.transfer,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.degree_eq_geometric_rank,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.pull_comparison,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.push_comparison,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.upstairs_columns,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.normalized_cycles,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.averageClass_empty,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.empty_does_not_supply_target,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.zero_mass_does_not_supply_target,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.model_satisfies_from_nonempty_finite_support,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.classMap,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.averageCycle,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.certificate,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.accepted,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.geometric_chow_push_pull,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.unchanged_model_basis_source_and_original_maps,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.actual_h0_source_and_original_point_evaluation,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.singleton_restriction_is_actual_pullback_and_evaluation,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.actual_delta_classes_restrict_to_the_same_singleton_units,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.point_deltas_reconstruct_original_h0_and_constant_mass,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.empty_support_has_zero_original_source_and_relative_target,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.relative_union_split_retains_actual_compatible_function_gluing,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.all_degree_support_extensions_are_original_composable_pair_maps,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.canonical_assembly_is_the_same_actual_bijection_in_every_degree,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.finite_gysin_components_are_original_point_restrictions_and_thom_maps,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.finite_gysin_is_an_iso_of_the_original_supported_target,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.point_delta_gysin_is_actual_singleton_support_extension,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.point_isomorphisms_use_original_finite_and_reciprocal_normal_charts,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.two_point_control_uses_actual_zero_and_infinity,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.balanced_original_h0_is_nonzero_with_zero_actual_mass,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.balanced_gysin_is_nonzero_in_original_supported_cohomology,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.balanced_support_forgetting_is_zero_and_is_not_injective,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.weighted_cycle_source_is_the_original_representative_and_ordinary_quotient,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.raw_cycle_and_quotient_use_the_same_actual_point_coefficients,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.original_supported_gysin_forgetting_matches_original_weighted_cycle_class,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.average_is_the_same_raw_cycle_before_the_original_quotient,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.nonempty_support_mass_and_average_supply_original_full_target,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.actual_global_degree_is_rank_at_a_selected_actual_support_point,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.every_nonempty_finite_support_has_same_full_model_certificate,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.concrete_two_point_normalization_uses_actual_cardinality_two,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.empty_and_zero_mass_classes_cannot_supply_the_full_target,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.unnormalized_push_fails_original_full_target_column,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification.degree_one_fails_and_normalization_recovers_original_average]
  unless declarations.length = 100 ∧ declarations.eraseDups.length = 100 do
    throwError "Expected exactly 100 distinct finite-support audit declarations"
  for declaration in declarations do
    unless env.contains declaration do
      throwError "Missing finite-support audit declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let assemblyEndpoint := `HodgeConjecture.SingularSupports.assemble_bijective
  let supportedEndpoints := [
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.supportedGysin_bijective,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.supported_difference_ne_zero]
  let forgetEndpoint := `HodgeConjecture.ProjectiveLineFiniteSupportGysin.forget_not_injective
  let nativeEndpoints := assemblyEndpoint :: supportedEndpoints ++ [forgetEndpoint]
  let forbiddenSquares := [
    `HodgeConjecture.Geometry.ProjectiveLineSquare,
    `HodgeConjecture.Realization.Betti.ProjectiveLineSquarePullback,
    `HodgeConjecture.Realization.Betti.ProjectiveLineSquareGysin,
    `HodgeConjecture.Realization.Betti.ProjectiveLineSquareRamification,
    `HodgeConjecture.Realization.Betti.Examples.ComplexSquareThom,
    `HodgeConjecture.Realization.Betti.Examples.CircleSquare]
  let forbiddenForgetting := [
    `HodgeConjecture.SingularSupports.forget,
    `HodgeConjecture.ProjectiveLineSupportedPoint.forget,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.gysin]
  unless nativeEndpoints.length = 4 ∧ supportedEndpoints.length = 2 ∧
      forbiddenSquares.length = 6 ∧ forbiddenForgetting.length = 3 do
    throwError "Expected four native boundaries, six old-square origins and three forgetting symbols"
  for name in forbiddenForgetting do
    unless env.contains name do
      throwError "Missing forgetting witness {name}"
  for endpoint in nativeEndpoints do
    unless env.contains endpoint do
      throwError "Missing finite-support native endpoint {endpoint}"
    let closure ← match projectDependencies env endpoint with
      | .ok closure => pure closure
      | .error message => throwError "{message}"
    let forbiddenUses := closure.toList.filter fun name ↦
      match env.getModuleIdxFor? name with
      | some idx =>
          let origin := env.header.moduleNames[idx]!
          let isAssembly := endpoint == assemblyEndpoint
          let isSupported := supportedEndpoints.contains endpoint
          let isGysinOrigin := decide (1 < (origin.toString.splitOn "Gysin").length)
          forbiddenSquares.contains origin ||
            (`HodgeConjecture.Realization.Chow).isPrefixOf origin ||
            (`HodgeConjecture.Realization.DeRham).isPrefixOf origin ||
            (isAssembly && ((`HodgeConjecture.Geometry).isPrefixOf origin || isGysinOrigin ||
              origin == `HodgeConjecture.Realization.Betti.ProjectiveLineSupportedPoint ||
              origin == `HodgeConjecture.Realization.Betti.Examples.ComplexPointThom)) ||
            (isSupported && origin == `HodgeConjecture.Realization.Betti.ProjectiveLineCohomology)
      | none => false
    unless forbiddenUses.isEmpty do
      throwError "Forbidden geometry/realization/absolute-coordinate route in {endpoint}: {forbiddenUses}"
    if supportedEndpoints.contains endpoint then
      for name in forbiddenForgetting do
        if closure.contains name then
          throwError "Supported bijection/nonzero proof {endpoint} used forgetting {name}"
    logInfo m!"PASS independent finite-support native core: {endpoint}"
  let forbiddenOldResults := [
    `HodgeConjecture.ProjectiveLineSquarePullback.cohomologyPullback_square,
    `HodgeConjecture.ProjectiveLineSquarePullback.cohomologyPullback_square_eq,
    `HodgeConjecture.ProjectiveLineSquarePullback.canonical_cohomologyPullback_square]
  let forbiddenFinalModules := [
    `HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage,
    `HodgeConjecture.Realization.DeRham.ProjectiveLineRamificationComparison,
    `HodgeConjecture.Realization.DeRham.ProjectiveLineFinitePointComparison,
    `HodgeConjecture.Realization.DeRham.ProjectiveLinePointGysinComparison]
  unless forbiddenOldResults.length = 3 ∧ forbiddenFinalModules.length = 4 do
    throwError "Expected three old global-square results and all four old aggregate fixtures"
  for witness in forbiddenOldResults ++
      [`HodgeConjecture.ProjectiveLineSquareCoverage.model_satisfies_from_square_cover,
       `HodgeConjecture.ProjectiveLineRamificationComparison.model_satisfies_from_ramification,
       `HodgeConjecture.ProjectiveLineFinitePointComparison.model_satisfies_from_finite_point,
       `HodgeConjecture.ProjectiveLinePointGysinComparison.model_satisfies_from_every_point] do
    unless env.contains witness do
      throwError "Missing old aggregate witness {witness}"
  let finalEndpoint :=
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.model_satisfies_from_nonempty_finite_support
  unless env.contains finalEndpoint do
    throwError "Missing finite-support aggregate endpoint {finalEndpoint}"
  let finalClosure ← match projectDependencies env finalEndpoint with
    | .ok closure => pure closure
    | .error message => throwError "{message}"
  for name in forbiddenOldResults do
    if finalClosure.contains name then
      throwError "Old global-square result entered finite-support endpoint: {name}"
  let oldFixtures := finalClosure.toList.filter fun name ↦
    match env.getModuleIdxFor? name with
    | some idx => forbiddenFinalModules.contains env.header.moduleNames[idx]!
    | none => false
  unless oldFixtures.isEmpty do
    throwError "Old aggregate fixture entered finite-support endpoint: {oldFixtures}"
  logInfo m!"PASS independent finite-support aggregate endpoint: {finalEndpoint}"
  let required := [
    `HodgeConjecture.RelativeUnionSplit.glueLinear,
    `HodgeConjecture.RelativeAdditivity.sumMap_bijective,
    `HodgeConjecture.SingularSupports.assemble_bijective,
    `HodgeConjecture.SingularFiniteSupport.pointRestriction,
    `HodgeConjecture.SingularFiniteSupport.pointCoordinates_pointRestriction,
    `HodgeConjecture.ProjectiveLineSupportedPoint.isoOfChart,
    `HodgeConjecture.ProjectiveLineFiniteSupportGysin.gysinEquiv_apply,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.supported_cycleClass_comparison,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.cycle,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.classMap,
    `HodgeConjecture.SchemeCycles.rationalClassMap,
    `HodgeConjecture.ProjectiveLineFiniteSupportComparison.mass_supportUnit,
    `HodgeConjecture.ProjectiveLineSquare.square_finrank]
  unless required.length = 13 ∧ required.eraseDups.length = 13 do
    throwError "Expected thirteen distinct actual finite-support construction dependencies"
  for name in required do
    unless env.contains name do
      throwError "Missing required finite-support dependency {name}"
    unless finalClosure.contains name do
      throwError "Required actual finite-support dependency {name} missing from {finalEndpoint}"
    logInfo m!"PASS required finite-support dependency: {name}"

end HodgeConjecture.ProjectiveLineFiniteSupportGysinVerification

end
