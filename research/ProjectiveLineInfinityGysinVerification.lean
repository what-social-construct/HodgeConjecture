module

public import HodgeConjecture.Realization.DeRham.ProjectiveLinePointGysinComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineRamificationComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineFinitePointComparison
public import HodgeConjecture.MathlibCompat.DeclarationDependencies
public import Mathlib.Tactic.NormNum
public import Lean.Util.CollectAxioms
public import Lean.Util.Path

-- Refresh with: python3 scripts/update_finite_point_audit_imports.py --audit research/ProjectiveLineInfinityGysinVerification.lean
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
import all HodgeConjecture.Realization.Betti.ProjectiveLineGysinCycleClass
import all HodgeConjecture.Realization.Betti.ProjectiveLineHodgeStructure
import all HodgeConjecture.Realization.Betti.ProjectiveLineInfinityGysin
import all HodgeConjecture.Realization.Betti.ProjectiveLineOrientation
import all HodgeConjecture.Realization.Betti.ProjectiveLinePointGysin
import all HodgeConjecture.Realization.Betti.ProjectiveLineProductClasses
import all HodgeConjecture.Realization.Betti.ProjectiveLineSquareGysin
import all HodgeConjecture.Realization.Betti.ProjectiveLineSquarePullback
import all HodgeConjecture.Realization.Betti.ProjectiveLineSquareRamification
import all HodgeConjecture.Realization.Betti.RationalDual
import all HodgeConjecture.Realization.Betti.RelativeCochains
import all HodgeConjecture.Realization.Betti.RelativeCochainsNaturality
import all HodgeConjecture.Realization.Betti.RelativeExcision
import all HodgeConjecture.Realization.Betti.RelativeMayerVietoris
import all HodgeConjecture.Realization.Betti.RelativeUnion
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

/-! Original reciprocal-chart Gysin, both native orientation signs, and the
same ordinary class/full-target certificate at every original native point. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineInfinityGysinVerification

open AlgebraicGeometry CategoryTheory HomologicalComplex Opposite Simplicial SchemeCycles
open ProjectiveLineComplexPoints ProjectiveLineAnalyticCover ProjectiveLineBettiCohomology
open ProjectiveLinePointGysinComparison

abbrev sampleCenter : ℂ := 1 + Complex.I

def negativeUnit : ℂˣ := Units.mk0 (-1 : ℂ) (by norm_num)
def imaginaryUnit : ℂˣ := Units.mk0 Complex.I (by norm_num)

private theorem class_coordinate (p : Point) : h2Equiv (model.cycleClass (pointClass p)) = 1 := by
  rw [pointClass_cycleClass, h2Equiv_coverGenerator]

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

theorem actual_second_scheme_chart_and_evaluation_are_retained (u : ℂˣ) (z : ℂ) :
    (ProjectiveLineInfinityChart.normalChart ℂ u).opensRange =
        (projectiveLineYChart ℂ).opensRange ∧
    ProjectiveLineAffineChart.affineSection ℂ z ≫ ProjectiveLineInfinityChart.normalChart ℂ u =
        ProjectiveLineInfinityChart.reciprocalSection ℂ ((u : ℂ) * z) ∧
    ProjectiveLineInfinityChart.normalChart ℂ u (affineLineOrigin ℂ) = projectiveLineInfinity ℂ :=
  ⟨ProjectiveLineInfinityChart.normalChart_opensRange ℂ u,
    ProjectiveLineInfinityChart.affineSection_normalChart ℂ z u,
    ProjectiveLineInfinityChart.normalChart_origin ℂ u⟩

theorem native_infinity_chart_is_the_same_actual_scheme_section (u : ℂˣ) (z : ℂ) :
    schemeMorphism (ProjectiveLineInfinityGysin.normalChartPoint u z) =
        ProjectiveLineAffineChart.affineSection ℂ z ≫ ProjectiveLineInfinityChart.normalChart ℂ u ∧
    ProjectiveLineInfinityGysin.normalChartPoint u z = reciprocal ((u : ℂ) * z) ∧
    schemeMorphism (ProjectiveLineInfinityGysin.normalChartPoint u 0)
      (default : Spec (.of ℂ)) = projectiveLineInfinity ℂ :=
  ⟨rfl, ProjectiveLineInfinityGysin.normalChartPoint_reciprocal u z,
    ProjectiveLineInfinityGysin.normalChart_center_base u _⟩

theorem reciprocal_is_actual_involution_switching_original_charts :
    Function.Involutive ProjectiveLineReciprocal.reciprocalMap ∧
    ProjectiveLineReciprocal.reciprocalMap (finite 0) = infinity ∧
    ProjectiveLineReciprocal.reciprocalMap infinity = finite 0 ∧
    ProjectiveLineReciprocal.reciprocalMap ⁻¹' reciprocalOpen = finiteOpen ∧
    ProjectiveLineReciprocal.reciprocalMap ⁻¹' finiteOpen = reciprocalOpen :=
  ⟨ProjectiveLineReciprocal.reciprocalMap_involutive,
    ProjectiveLineReciprocal.reciprocalMap_zero, ProjectiveLineReciprocal.reciprocalMap_infinity,
    ProjectiveLineReciprocal.preimage_reciprocalOpen, ProjectiveLineReciprocal.preimage_finiteOpen⟩

theorem original_cochain_difference_forces_the_cover_swap_sign
    {S : SSet.{0}} (A B : S.Subcomplex) :
    SubcomplexCochains.coverDifference A B ≫
        (-SingularMayerVietorisSwap.intersectionPullback A B) =
      SingularMayerVietorisSwap.pairSwap A B ≫ SubcomplexCochains.coverDifference B A ∧
    SingularMayerVietorisSwap.intersectionSwap (TopCat.of Point) finiteOpen reciprocalOpen ≫
      SingularMayerVietorisSwap.intersectionSwap (TopCat.of Point) reciprocalOpen finiteOpen = 𝟙 _ :=
  ⟨SingularMayerVietorisSwap.coverDifference_swap A B,
    SingularMayerVietorisSwap.intersectionSwap_comp _ _ _⟩

theorem circle_overlap_inversion_exchanges_actual_components
    (z : SingularCochains.Cohomology (TopCat.of CircleTopology.overlap) 0) (i : Bool) :
    CircleInversion.overlapMap (CircleTopology.overlapPoint i) = CircleTopology.overlapPoint (!i) ∧
    CircleCohomology.overlapZeroEquiv
        (SingularCochains.cohomologyPullback CircleInversion.overlapMap 0 z) i =
      CircleCohomology.overlapZeroEquiv z (!i) :=
  ⟨CircleInversion.overlapMap_point i, CircleInversion.overlap_coordinates z i⟩

theorem actual_circle_and_projective_overlap_pullback_are_negative
    (z : SingularCochains.Cohomology CircleInversion.space 1)
    (w : SingularCochains.Cohomology (TopCat.of ProjectiveLineReciprocal.Overlap) 1) :
    SingularCochains.cohomologyPullback CircleInversion.inversionMap 1 z = -z ∧
    SingularCochains.cohomologyPullback ProjectiveLineReciprocal.overlapMap 1 w = -w :=
  ⟨CircleInversion.cohomologyPullback_inversion z,
    ProjectiveLineReciprocal.overlap_cohomologyPullback w⟩

theorem two_original_orientation_signs_give_positive_native_h2
    (z : SingularCochains.Cohomology ProjectiveLineReciprocal.space 2) :
    SingularCochains.cohomologyPullback ProjectiveLineReciprocal.reciprocalMap 2 =
        𝟙 (SingularCochains.Cohomology ProjectiveLineReciprocal.space 2) ∧
    SingularCochains.cohomologyPullback ProjectiveLineReciprocal.reciprocalMap 2 z = z :=
  ⟨ProjectiveLineReciprocal.cohomologyPullback_reciprocal_two,
    ProjectiveLineReciprocal.cohomologyPullback_reciprocal_apply z⟩

theorem omitting_the_cover_swap_sign_fails_on_the_original_boundary :
    ProjectiveLineReciprocal.reversedConnecting
        (SingularCochains.cohomologyPullback
          (SingularMayerVietorisSwap.intersectionSwap (TopCat.of Point) reciprocalOpen finiteOpen) 1
            ProjectiveLineNormalChart.overlapOrientationClass) = -coverGenerator ∧
    ProjectiveLineReciprocal.reversedConnecting
        (SingularCochains.cohomologyPullback
          (SingularMayerVietorisSwap.intersectionSwap (TopCat.of Point) reciprocalOpen finiteOpen) 1
            ProjectiveLineNormalChart.overlapOrientationClass) ≠ coverGenerator := by
  have h := SingularMayerVietorisSwap.connecting_swap_apply (TopCat.of Point)
    reciprocalOpen finiteOpen isOpen_reciprocalOpen isOpen_finiteOpen
    ProjectiveLineReciprocal.reversed_cover 1 ProjectiveLineNormalChart.overlapOrientationClass
  change ProjectiveLineReciprocal.reversedConnecting _ = -coverGenerator at h
  refine ⟨h, ?_⟩
  intro hwrong
  have hc := congrArg h2Equiv (h.symm.trans hwrong)
  rw [map_neg, h2Equiv_coverGenerator] at hc
  norm_num at hc

theorem actual_infinity_support_unit_and_scheme_image_are_retained :
    ProjectiveLineInfinitySupport.complement = ProjectiveLineInfinitySupport.supportᶜ ∧
    ProjectiveLineInfinitySupport.pointCoordinates ProjectiveLineInfinitySupport.pointUnit = 1 ∧
    schemeMorphism ProjectiveLineInfinitySupport.point.val (default : Spec (.of ℂ)) =
      projectiveLineInfinity ℂ :=
  ⟨ProjectiveLineInfinitySupport.complement_eq,
    ProjectiveLineInfinitySupport.pointCoordinates_pointUnit,
    ProjectiveLineInfinitySupport.pointSupport_scheme_base _ _⟩

theorem negative_and_imaginary_infinity_coordinates_keep_actual_center :
    ProjectiveLineInfinityGysin.normalChartPoint negativeUnit 1 = reciprocal (-1) ∧
    ProjectiveLineInfinityGysin.normalChartPoint imaginaryUnit 1 = reciprocal Complex.I ∧
    ProjectiveLineInfinityGysin.normalChartPoint imaginaryUnit 0 = infinity := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [ProjectiveLineInfinityGysin.normalChartPoint_reciprocal, mul_one]
    rfl
  · simp only [ProjectiveLineInfinityGysin.normalChartPoint_reciprocal, mul_one]
    rfl
  · simp only [ProjectiveLineInfinityGysin.normalChartPoint_reciprocal, mul_zero]
    rfl

theorem infinity_original_relative_excision_and_forget_diagrams (u : ℂˣ) :
    RelativeExcision.restriction ProjectiveLineInfinityGysin.first ProjectiveLineInfinityGysin.second ≫
        (ProjectiveLineInfinityGysin.normalPullbackIso u).hom =
      ProjectiveLineInfinityGysin.chartPullback u ∧
    (ProjectiveLineInfinityGysin.chartComparison u 2).hom =
      homologyMap (ProjectiveLineInfinityGysin.chartPullback u) 2 ∧
    ProjectiveLineInfinityGysin.supportedPull u 2 ≫
        RelativeCochains.forget ProjectiveLinePointGysin.complementSubcomplex 2 =
      RelativeCochains.forget ProjectiveLineInfinityGysin.second 2 ≫
        SingularCochains.cohomologyPullback (ProjectiveLineInfinityGysin.transportMap u) 2 :=
  ⟨ProjectiveLineInfinityGysin.chartPullback_eq_original u,
    ProjectiveLineInfinityGysin.chartComparison_hom u 2,
    ProjectiveLineInfinityGysin.supportedPull_forget u 2⟩

theorem actual_infinity_gysin_iso_has_original_positive_unit (u : ℂˣ) :
    (ProjectiveLineInfinityGysin.gysinIso u).hom ProjectiveLineInfinitySupport.pointUnit = coverGenerator ∧
    RelativeCochains.forget ProjectiveLineInfinityGysin.second 2
        (ProjectiveLineInfinityGysin.supportedThomClass u) = coverGenerator ∧
    ProjectiveLineInfinityGysin.supportedGysin u ProjectiveLineInfinitySupport.pointUnit =
      ProjectiveLineInfinityGysin.supportedThomClass u := by
  refine ⟨?_, ProjectiveLineInfinityGysin.forget_supportedThomClass u,
    ProjectiveLineInfinityGysin.supportedGysin_pointUnit u⟩
  rw [ProjectiveLineInfinityGysin.gysinIso_apply, ProjectiveLineInfinityGysin.gysin_pointUnit]

theorem original_gysin_maps_are_independent_of_both_chart_scales :
    ProjectiveLineInfinityGysin.supportedGysin negativeUnit =
        ProjectiveLineInfinityGysin.supportedGysin imaginaryUnit ∧
    ProjectiveLineInfinityGysin.gysin imaginaryUnit = ProjectiveLineInfinityGysin.gysin 1 ∧
    ProjectiveLineFinitePointGysin.gysin sampleCenter negativeUnit =
      ProjectiveLineFinitePointGysin.gysin sampleCenter imaginaryUnit :=
  ⟨ProjectiveLineInfinityGysin.supportedGysin_coordinate_independent _ _,
    ProjectiveLineInfinityGysin.gysin_coordinate_independent _ _,
    ProjectiveLineFinitePointGysin.gysin_coordinate_independent _ _ _⟩

theorem negative_infinity_point_unit_does_not_have_positive_normalization (u : ℂˣ) :
    ProjectiveLineInfinityGysin.gysin u ProjectiveLineInfinitySupport.pointUnit ≠ 0 ∧
    ProjectiveLineInfinityGysin.gysin u (-ProjectiveLineInfinitySupport.pointUnit) ≠ coverGenerator := by
  constructor
  · intro h
    have hc := congrArg h2Equiv h
    rw [ProjectiveLineInfinityGysin.gysin_pointUnit, h2Equiv_coverGenerator, map_zero] at hc
    norm_num at hc
  · intro h
    have hc := congrArg h2Equiv h
    rw [map_neg, ProjectiveLineInfinityGysin.gysin_pointUnit,
      map_neg, h2Equiv_coverGenerator] at hc
    norm_num at hc

theorem every_original_point_has_geometric_gysin_and_scale_independence (p : Point) (u : ℂˣ) :
    (∃ e : ProjectiveLineInfinityGysin.PointH0At p ≅ Betti,
      e.hom (ProjectiveLineInfinityGysin.pointUnitAt p) = coverGenerator) ∧
    ∃ g : ℂˣ → (ProjectiveLineInfinityGysin.PointH0At p →ₗ[ℚ] Betti),
      (∀ v, g v (ProjectiveLineInfinityGysin.pointUnitAt p) = coverGenerator) ∧
      (∀ v w, g v = g w) :=
  ⟨ProjectiveLineInfinityGysin.every_point_gysinIso p u,
    ProjectiveLineInfinityGysin.every_point_scale_independent p⟩

theorem original_finite_and_infinity_scheme_images_and_chow_classes (a : ℂ) :
    schemePoint (finite a) = ProjectiveLineAffineChart.center ℂ a ∧
    schemePoint infinity = projectiveLineInfinity ℂ ∧
    pointClass (finite a) = ProjectiveLineFinitePointChow.pointClass ℂ a ∧
    pointClass infinity = ProjectiveLineCycles.Infinity.rationalClass ℂ :=
  ⟨schemePoint_finite a, schemePoint_infinity, pointClass_finite a, pointClass_infinity⟩

theorem transfer_degree_is_original_global_rank_at_every_selected_point (p : Point) :
    (transfer p).degree = cover.finrank (schemePoint p) ∧
    (transfer p).degree = 2 ∧
    ∀ x : scheme, (transfer p).degree = cover.finrank x :=
  ⟨rfl, degree_eq_two p, degree_eq_geometric_rank p⟩

theorem every_original_point_has_the_same_full_target_certificate (p : Point) :
    FiniteCoverageCertificate.check (certificate p) = true ∧
    (certificate p).cycles () = pointClass p ∧
    RationalHodgeConjectureAt ProjectiveLineCoverageCertificate.model :=
  ⟨accepted p, normalized_cycles p (), model_satisfies_from_every_point p⟩

theorem infinity_normalization_recovers_original_infinity_class :
    (certificate infinity).cycles () = ProjectiveLineCycles.Infinity.rationalClass ℂ ∧
    model.cycleClass (pointClass infinity) = coverGenerator ∧ pointClass infinity ≠ 0 :=
  ⟨normalized_cycles_infinity (), pointClass_cycleClass infinity, pointClass_ne_zero infinity⟩

theorem nonzero_finite_sample_keeps_its_actual_point_and_original_class :
    schemePoint (finite sampleCenter) = ProjectiveLineAffineChart.center ℂ sampleCenter ∧
    (certificate (finite sampleCenter)).cycles () =
      ProjectiveLineFinitePointChow.pointClass ℂ sampleCenter :=
  ⟨schemePoint_finite sampleCenter, normalized_cycles_finite sampleCenter ()⟩

theorem geometric_gysin_unit_is_the_same_original_cycle_class (p : Point) (u : ℂˣ) :
    ∃ e : ProjectiveLineInfinityGysin.PointH0At p ≅ Betti,
      e.hom (ProjectiveLineInfinityGysin.pointUnitAt p) = model.cycleClass (pointClass p) ∧
      e.hom (ProjectiveLineInfinityGysin.pointUnitAt p) = coverGenerator :=
  geometric_gysin_unit p u

theorem unnormalized_push_fails_the_original_full_target_column (p : Point) :
    model.cycleClass (actualPush (upstairsCycles p ())) ≠
      (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i ()) : Betti) := by
  intro h
  have hc := congrArg h2Equiv h
  change h2Equiv (model.cycleClass (actualPush (actualPull (pointClass p)))) = _ at hc
  rw [geometric_chow_push_pull p, map_smul, map_smul, class_coordinate,
    degree_eq_two, target_column, h2Equiv_coverGenerator] at hc
  norm_num at hc

theorem degree_one_fails_and_normalization_recovers_the_same_original_point (p : Point) :
    (¬ ∀ z : Betti, (transfer p).push ((transfer p).pull z) = (1 : ℚ) • z) ∧
    (((transfer p).degree : ℚ)⁻¹ • actualPush (actualPull (pointClass p)) = pointClass p) := by
  constructor
  · intro h
    have htwo : (transfer p).push ((transfer p).pull (model.cycleClass (pointClass p))) =
        ((transfer p).degree : ℚ) • model.cycleClass (pointClass p) := by
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (transfer p).push_comp_pull (model.cycleClass (pointClass p))
    have hc := congrArg h2Equiv (h (model.cycleClass (pointClass p)))
    rw [htwo, one_smul, map_smul, class_coordinate, degree_eq_two] at hc
    norm_num at hc
  · rw [geometric_chow_push_pull p, smul_smul, degree_eq_two]
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
    `HodgeConjecture.SingularMayerVietorisSwap.coverRestriction_swap,
    `HodgeConjecture.SingularMayerVietorisSwap.coverDifference_swap,
    `HodgeConjecture.SingularMayerVietorisSwap.coverShortComplexSwap,
    `HodgeConjecture.SingularMayerVietorisSwap.subcomplex_connecting_swap,
    `HodgeConjecture.SingularMayerVietorisSwap.connecting_swap,
    `HodgeConjecture.SingularMayerVietorisSwap.connecting_swap_apply,
    `HodgeConjecture.CircleInversion.overlapMap_point,
    `HodgeConjecture.CircleInversion.overlap_coordinates,
    `HodgeConjecture.CircleInversion.connecting_naturality,
    `HodgeConjecture.CircleInversion.cohomologyPullback_inversion,
    `HodgeConjecture.CircleInversion.cohomologyPullback_inversion_eq,
    `HodgeConjecture.ProjectiveLineReciprocal.reciprocalMap_involutive,
    `HodgeConjecture.ProjectiveLineReciprocal.preimage_reciprocalOpen,
    `HodgeConjecture.ProjectiveLineReciprocal.preimage_finiteOpen,
    `HodgeConjecture.ProjectiveLineReciprocal.circleInclusion_inversion,
    `HodgeConjecture.ProjectiveLineReciprocal.overlap_cohomologyPullback,
    `HodgeConjecture.ProjectiveLineReciprocal.cohomologyPullback_reciprocal_apply,
    `HodgeConjecture.ProjectiveLineReciprocal.cohomologyPullback_reciprocal_two,
    `HodgeConjecture.ProjectiveLineInfinityChart.normalChart_over_base,
    `HodgeConjecture.ProjectiveLineInfinityChart.affineSection_normalChart,
    `HodgeConjecture.ProjectiveLineInfinityChart.normalChart_origin,
    `HodgeConjecture.ProjectiveLineInfinityChart.infinitySection_base,
    `HodgeConjecture.ProjectiveLineInfinityChart.infinity_isClosed,
    `HodgeConjecture.ProjectiveLineInfinitySupport.complement_eq,
    `HodgeConjecture.ProjectiveLineInfinitySupport.reciprocal_mem_complement_iff,
    `HodgeConjecture.ProjectiveLineInfinitySupport.pointNormalHomeomorph_coe,
    `HodgeConjecture.ProjectiveLineInfinitySupport.pointSupport_scheme_base,
    `HodgeConjecture.ProjectiveLineInfinitySupport.pointCoordinates_pointUnit,
    `HodgeConjecture.ProjectiveLineInfinityGysin.normalChartPoint_reciprocal,
    `HodgeConjecture.ProjectiveLineInfinityGysin.normalSSetIso_inclusion,
    `HodgeConjecture.ProjectiveLineInfinityGysin.punctured_preimage,
    `HodgeConjecture.ProjectiveLineInfinityGysin.chartPullback_eq_original,
    `HodgeConjecture.ProjectiveLineInfinityGysin.chartComparison_hom,
    `HodgeConjecture.ProjectiveLineInfinityGysin.thomToSupportIso,
    `HodgeConjecture.ProjectiveLineInfinityGysin.forget_isIso,
    `HodgeConjecture.ProjectiveLineInfinityGysin.relativePullback_chart,
    `HodgeConjecture.ProjectiveLineInfinityGysin.supportedPull_forget,
    `HodgeConjecture.ProjectiveLineInfinityGysin.supportedPull_thomClass,
    `HodgeConjecture.ProjectiveLineInfinityGysin.cohomologyPullback_transport_two,
    `HodgeConjecture.ProjectiveLineInfinityGysin.forget_supportedThomClass,
    `HodgeConjecture.ProjectiveLineInfinityGysin.gysin_pointUnit,
    `HodgeConjecture.ProjectiveLineInfinityGysin.gysinIso_apply,
    `HodgeConjecture.ProjectiveLineInfinityGysin.gysin_coordinate_independent,
    `HodgeConjecture.ProjectiveLineInfinityGysin.supportedGysin_coordinate_independent,
    `HodgeConjecture.ProjectiveLineInfinityGysin.every_point_gysinIso,
    `HodgeConjecture.ProjectiveLineInfinityGysin.every_point_scale_independent,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.schemePoint_infinity,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.pointClass_finite,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.pointClass_infinity,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.geometric_gysin_unit,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.pointClass_cycleClass,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.transfer,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.degree_eq_geometric_rank,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.pull_comparison,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.push_comparison,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.upstairs_columns,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.normalized_cycles,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.normalized_cycles_infinity,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.accepted,
    `HodgeConjecture.ProjectiveLinePointGysinComparison.model_satisfies_from_every_point,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.unchanged_model_basis_source_and_original_maps,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.actual_second_scheme_chart_and_evaluation_are_retained,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.native_infinity_chart_is_the_same_actual_scheme_section,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.reciprocal_is_actual_involution_switching_original_charts,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.original_cochain_difference_forces_the_cover_swap_sign,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.circle_overlap_inversion_exchanges_actual_components,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.actual_circle_and_projective_overlap_pullback_are_negative,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.two_original_orientation_signs_give_positive_native_h2,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.omitting_the_cover_swap_sign_fails_on_the_original_boundary,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.actual_infinity_support_unit_and_scheme_image_are_retained,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.negative_and_imaginary_infinity_coordinates_keep_actual_center,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.infinity_original_relative_excision_and_forget_diagrams,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.actual_infinity_gysin_iso_has_original_positive_unit,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.original_gysin_maps_are_independent_of_both_chart_scales,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.negative_infinity_point_unit_does_not_have_positive_normalization,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.every_original_point_has_geometric_gysin_and_scale_independence,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.original_finite_and_infinity_scheme_images_and_chow_classes,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.transfer_degree_is_original_global_rank_at_every_selected_point,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.every_original_point_has_the_same_full_target_certificate,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.infinity_normalization_recovers_original_infinity_class,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.nonzero_finite_sample_keeps_its_actual_point_and_original_class,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.geometric_gysin_unit_is_the_same_original_cycle_class,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.unnormalized_push_fails_the_original_full_target_column,
    `HodgeConjecture.ProjectiveLineInfinityGysinVerification.degree_one_fails_and_normalization_recovers_the_same_original_point]
  unless declarations.length = 84 ∧ declarations.eraseDups.length = 84 do
    throwError "Expected exactly 84 distinct infinity/every-point audit declarations"
  for declaration in declarations do
    unless env.contains declaration do
      throwError "Missing infinity/every-point audit declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbiddenCoreModules := [
    `HodgeConjecture.Geometry.ProjectiveLineSquare,
    `HodgeConjecture.Realization.Betti.ProjectiveLineSquarePullback,
    `HodgeConjecture.Realization.Betti.ProjectiveLineSquareGysin,
    `HodgeConjecture.Realization.Betti.ProjectiveLineSquareRamification,
    `HodgeConjecture.Realization.Betti.Examples.ComplexSquareThom,
    `HodgeConjecture.Realization.Betti.Examples.CircleSquare]
  let reciprocalEndpoint := `HodgeConjecture.ProjectiveLineReciprocal.cohomologyPullback_reciprocal_two
  let coreEndpoints := [reciprocalEndpoint,
    `HodgeConjecture.ProjectiveLineInfinityGysin.gysin_pointUnit,
    `HodgeConjecture.ProjectiveLineInfinityGysin.supportedGysin_coordinate_independent]
  unless forbiddenCoreModules.length = 6 ∧ coreEndpoints.length = 3 do
    throwError "Expected six forbidden square origins and three native endpoints"
  for witness in [`HodgeConjecture.ProjectiveLineBettiCohomology.h2Equiv,
      `HodgeConjecture.ProjectiveLineBettiCohomology.coverGenerator] do
    unless env.contains witness do
      throwError "Missing absolute-coordinate witness {witness}"
  for endpoint in coreEndpoints do
    unless env.contains endpoint do
      throwError "Missing infinity/reciprocal native endpoint {endpoint}"
    let closure ← match projectDependencies env endpoint with
      | .ok closure => pure closure
      | .error message => throwError "{message}"
    let forbiddenUses := closure.toList.filter fun name ↦
      match env.getModuleIdxFor? name with
      | some idx =>
          let origin := env.header.moduleNames[idx]!
          forbiddenCoreModules.contains origin ||
            (`HodgeConjecture.Realization.Chow).isPrefixOf origin ||
            (`HodgeConjecture.Realization.DeRham).isPrefixOf origin ||
            (endpoint == reciprocalEndpoint &&
              origin == `HodgeConjecture.Realization.Betti.ProjectiveLineCohomology)
      | none => false
    unless forbiddenUses.isEmpty do
      throwError "Forbidden square/realization/absolute-coordinate dependency in {endpoint}: {forbiddenUses}"
    logInfo m!"PASS independent infinity/reciprocal native core: {endpoint}"
  let forbiddenOldResults := [
    `HodgeConjecture.ProjectiveLineSquarePullback.cohomologyPullback_square,
    `HodgeConjecture.ProjectiveLineSquarePullback.cohomologyPullback_square_eq,
    `HodgeConjecture.ProjectiveLineSquarePullback.canonical_cohomologyPullback_square]
  let forbiddenFinalModules := [
    `HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage,
    `HodgeConjecture.Realization.DeRham.ProjectiveLineRamificationComparison,
    `HodgeConjecture.Realization.DeRham.ProjectiveLineFinitePointComparison]
  unless forbiddenOldResults.length = 3 ∧ forbiddenFinalModules.length = 3 do
    throwError "Expected three old global results and three old fixture origins"
  for witness in forbiddenOldResults ++
      [`HodgeConjecture.ProjectiveLineSquareCoverage.model_satisfies_from_square_cover,
       `HodgeConjecture.ProjectiveLineRamificationComparison.model_satisfies_from_ramification,
       `HodgeConjecture.ProjectiveLineFinitePointComparison.model_satisfies_from_finite_point] do
    unless env.contains witness do
      throwError "Missing old-result witness for every-point dependency guard {witness}"
  let finalEndpoint := `HodgeConjecture.ProjectiveLinePointGysinComparison.model_satisfies_from_every_point
  unless env.contains finalEndpoint do
    throwError "Missing every-point family endpoint {finalEndpoint}"
  let finalClosure ← match projectDependencies env finalEndpoint with
    | .ok closure => pure closure
    | .error message => throwError "{message}"
  for name in forbiddenOldResults do
    if finalClosure.contains name then
      throwError "Old absolute-square result {name} entered every-point endpoint"
  let forbiddenFixtures := finalClosure.toList.filter fun name ↦
    match env.getModuleIdxFor? name with
    | some idx => forbiddenFinalModules.contains env.header.moduleNames[idx]!
    | none => false
  unless forbiddenFixtures.isEmpty do
    throwError "Old fixture declarations entered every-point endpoint: {forbiddenFixtures}"
  logInfo m!"PASS independent every-point Gysin endpoint: {finalEndpoint}"
  let required := [
    `HodgeConjecture.ProjectiveLineInfinityChart.affineSection_normalChart,
    `HodgeConjecture.ProjectiveLineInfinitySupport.pointSupport_scheme_base,
    `HodgeConjecture.SingularMayerVietorisSwap.connecting_swap,
    `HodgeConjecture.CircleInversion.cohomologyPullback_inversion,
    `HodgeConjecture.ProjectiveLineReciprocal.cohomologyPullback_reciprocal_two,
    `HodgeConjecture.ProjectiveLineInfinityGysin.chartPullback_eq_original,
    `HodgeConjecture.ProjectiveLineInfinityGysin.gysin_pointUnit,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.gysin_pointUnit,
    `HodgeConjecture.ProjectiveLineInfinityGysin.every_point_gysinIso,
    `HodgeConjecture.ProjectiveLineSquare.square_finrank]
  unless required.length = 10 do
    throwError "Expected ten actual scheme/support/MV/orientation/Gysin/global-rank dependencies"
  for name in required do
    unless env.contains name do
      throwError "Missing required every-point dependency {name}"
    unless finalClosure.contains name do
      throwError "Required actual every-point dependency {name} missing from {finalEndpoint}"
    logInfo m!"PASS required every-point dependency: {name}"

end HodgeConjecture.ProjectiveLineInfinityGysinVerification

end
