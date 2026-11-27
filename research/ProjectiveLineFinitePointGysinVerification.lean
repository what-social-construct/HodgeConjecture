module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineFinitePointComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineRamificationComparison
public import HodgeConjecture.MathlibCompat.DeclarationDependencies
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Lean.Util.CollectAxioms
public import Lean.Util.Path

-- Refresh with: python3 scripts/update_finite_point_audit_imports.py
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
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineNormalChart
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLineNormalChartBoundary
import all HodgeConjecture.Realization.Betti.Examples.ProjectiveLinePointSupport
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

/-! Finite-point Gysin controls retain the actual scheme normal chart,
original relative maps, positive complex orientation and original ordinary
point classes. Old fixtures are available but excluded from the audited
new proof closures. Global square rank is distinguished from local length. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineFinitePointGysinVerification

open AlgebraicGeometry CategoryTheory HomologicalComplex Opposite Simplicial SchemeCycles
open ProjectiveLineComplexPoints ProjectiveLineAnalyticCover ProjectiveLineBettiCohomology
open ProjectiveLineFinitePointComparison

abbrev sampleCenter : ℂ := 1 + Complex.I

def negativeUnit : ℂˣ := Units.mk0 (-1 : ℂ) (by norm_num)
def imaginaryUnit : ℂˣ := Units.mk0 Complex.I (by norm_num)

private theorem class_coordinate (a : ℂ) : h2Equiv (model.cycleClass (pointClass a)) = 1 := by
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

theorem actual_affine_scheme_iso_keeps_original_chart_range
    (a : ℂ) (u : ℂˣ) (z : ℂ) :
    IsIso (ProjectiveLineAffineChart.affineIso ℂ a u).hom ∧
    (ProjectiveLineAffineChart.normalChart ℂ a u).opensRange =
      (projectiveLineXChart ℂ).opensRange ∧
    ProjectiveLineAffineChart.affineSection ℂ z ≫
        ProjectiveLineAffineChart.normalChart ℂ a u =
      ProjectiveLineAffineChart.finiteSection ℂ (a + (u : ℂ) * z) :=
  ⟨inferInstance, ProjectiveLineAffineChart.normalChart_opensRange ℂ a u,
    ProjectiveLineAffineChart.affineSection_normalChart ℂ a z u⟩

theorem native_chart_is_the_same_actual_scheme_section
    (a : ℂ) (u : ℂˣ) (z : ℂ) :
    schemeMorphism (ProjectiveLineFinitePointGysin.normalChartPoint a u z) =
        ProjectiveLineAffineChart.affineSection ℂ z ≫
          ProjectiveLineAffineChart.normalChart ℂ a u ∧
    ProjectiveLineFinitePointGysin.normalChartPoint a u z = finite (a + (u : ℂ) * z) ∧
    schemeMorphism (ProjectiveLineFinitePointGysin.normalChartPoint a u 0)
        (default : Spec (.of ℂ)) = ProjectiveLineAffineChart.center ℂ a :=
  ⟨rfl, ProjectiveLineFinitePointGysin.normalChartPoint_finite a u z,
    ProjectiveLineFinitePointGysin.normalChart_center_base a u _⟩

theorem nontrivial_negative_and_imaginary_chart_samples :
    ProjectiveLineFinitePointGysin.normalChartPoint sampleCenter negativeUnit 1 = finite Complex.I ∧
    ProjectiveLineFinitePointGysin.normalChartPoint sampleCenter imaginaryUnit 1 =
      finite (1 + 2 * Complex.I) ∧
    ProjectiveLineAffine.affineMap sampleCenter imaginaryUnit infinity = infinity := by
  refine ⟨?_, ?_, ProjectiveLineAffine.affineMap_infinity _ _⟩
  · rw [ProjectiveLineFinitePointGysin.normalChartPoint_finite]
    congr 1
    norm_num [sampleCenter, negativeUnit]
  · rw [ProjectiveLineFinitePointGysin.normalChartPoint_finite]
    congr 1
    norm_num [sampleCenter, imaginaryUnit]
    ring

theorem actual_affine_homotopy_keeps_finite_endpoints_and_infinity
    (a : ℂ) (u : ℂˣ) (t : unitInterval) (z : ℂ) :
    ProjectiveLineAffine.affineHomotopy a u (0, finite z) = finite z ∧
    ProjectiveLineAffine.affineHomotopy a u (1, finite z) = finite (a + (u : ℂ) * z) ∧
    ProjectiveLineAffine.affineHomotopy a u (t, infinity) = infinity := by
  constructor
  · exact (ProjectiveLineAffine.affineHomotopy a u).map_zero_left (finite z)
  constructor
  · have h := (ProjectiveLineAffine.affineHomotopy a u).map_one_left (finite z)
    change (ProjectiveLineAffine.affineHomotopy a u) (1, finite z) =
      ProjectiveLineAffine.affineHomeomorph a u (finite z) at h
    exact h.trans (ProjectiveLineAffine.affineHomeomorph_finite a u z)
  · exact ProjectiveLineAffine.affineHomotopyFun_infinity a u t

theorem rotated_affine_samples_act_identically_in_every_native_degree
    (n : ℕ) (z : SingularCochains.Cohomology ProjectiveLineAffine.space n) :
    SingularCochains.cohomologyPullback (ProjectiveLineAffine.affineMap sampleCenter negativeUnit) n z = z ∧
    SingularCochains.cohomologyPullback (ProjectiveLineAffine.affineMap sampleCenter imaginaryUnit) n z = z :=
  ⟨ProjectiveLineAffine.cohomologyPullback_affine_apply _ _ _ _,
    ProjectiveLineAffine.cohomologyPullback_affine_apply _ _ _ _⟩

theorem actual_complement_and_normal_point_maps_agree
    (a : ℂ) (u : ℂˣ) (x : ComplexPointThom.Point) :
    ProjectiveLineAffine.affineMap a u ⁻¹' ProjectiveLineFinitePointSupport.complement a =
      reciprocalOpen ∧
    (ProjectiveLineFinitePointSupport.pointNormalHomeomorph a x : Point) =
      ProjectiveLineFinitePointGysin.normalChartPoint a u x.val := by
  refine ⟨ProjectiveLineFinitePointSupport.preimage_complement a u, ?_⟩
  rw [ProjectiveLineFinitePointSupport.pointNormalHomeomorph_coe,
    ProjectiveLineFinitePointGysin.normalChartPoint_finite,
    Set.mem_singleton_iff.mp x.property, mul_zero, add_zero]

theorem actual_singleton_unit_and_scheme_image_are_retained (a : ℂ) :
    ContractibleSpace ↥(ProjectiveLineFinitePointSupport.complement a) ∧
    ProjectiveLineFinitePointSupport.pointCoordinates a
        (ProjectiveLineFinitePointSupport.pointUnit a) = 1 ∧
    schemeMorphism (ProjectiveLineFinitePointSupport.point a).val
        (default : Spec (.of ℂ)) = ProjectiveLineAffineChart.center ℂ a :=
  ⟨inferInstance, ProjectiveLineFinitePointSupport.pointCoordinates_pointUnit a,
    ProjectiveLineFinitePointGysin.pointSupport_scheme_base a _ _⟩

theorem original_relative_chart_excision_and_forget_maps_are_retained
    (a : ℂ) (u : ℂˣ) :
    RelativeExcision.restriction ProjectiveLineFinitePointGysin.first
        (ProjectiveLineFinitePointGysin.second a) ≫
        (ProjectiveLineFinitePointGysin.normalPullbackIso a u).hom =
      ProjectiveLineFinitePointGysin.chartPullback a u ∧
    (ProjectiveLineFinitePointGysin.chartComparison a u 2).hom =
      homologyMap (ProjectiveLineFinitePointGysin.chartPullback a u) 2 ∧
    ProjectiveLineFinitePointGysin.affineSupportedPull a u 2 ≫
        RelativeCochains.forget ProjectiveLinePointGysin.complementSubcomplex 2 =
      RelativeCochains.forget (ProjectiveLineFinitePointGysin.second a) 2 ≫
        SingularCochains.cohomologyPullback (ProjectiveLineAffine.affineMap a u) 2 :=
  ⟨ProjectiveLineFinitePointGysin.chartPullback_eq_original a u,
    ProjectiveLineFinitePointGysin.chartComparison_hom a u 2,
    ProjectiveLineFinitePointGysin.affineSupportedPull_forget a u 2⟩

theorem actual_gysin_iso_has_positive_original_unit (a : ℂ) (u : ℂˣ) :
    (ProjectiveLineFinitePointGysin.gysinIso a u).hom
        (ProjectiveLineFinitePointSupport.pointUnit a) = coverGenerator ∧
    RelativeCochains.forget (ProjectiveLineFinitePointGysin.second a) 2
        (ProjectiveLineFinitePointGysin.supportedThomClass a u) = coverGenerator ∧
    ProjectiveLineFinitePointGysin.supportedGysin a u
        (ProjectiveLineFinitePointSupport.pointUnit a) =
      ProjectiveLineFinitePointGysin.supportedThomClass a u := by
  refine ⟨?_, ProjectiveLineFinitePointGysin.forget_supportedThomClass a u,
    ProjectiveLineFinitePointGysin.supportedGysin_pointUnit a u⟩
  rw [ProjectiveLineFinitePointGysin.gysinIso_apply, ProjectiveLineFinitePointGysin.gysin_pointUnit]

theorem complex_negative_and_imaginary_units_preserve_positive_orientation :
    ProjectiveLineFinitePointGysin.supportedGysin sampleCenter negativeUnit =
      ProjectiveLineFinitePointGysin.supportedGysin sampleCenter imaginaryUnit ∧
    ProjectiveLineFinitePointGysin.gysin sampleCenter imaginaryUnit =
      ProjectiveLineFinitePointGysin.gysin sampleCenter 1 ∧
    h2Equiv (ProjectiveLineFinitePointGysin.gysin sampleCenter negativeUnit
      (ProjectiveLineFinitePointSupport.pointUnit sampleCenter)) = 1 := by
  refine ⟨ProjectiveLineFinitePointGysin.supportedGysin_coordinate_independent _ _ _,
    ProjectiveLineFinitePointGysin.gysin_coordinate_independent _ _ _, ?_⟩
  rw [ProjectiveLineFinitePointGysin.gysin_pointUnit, h2Equiv_coverGenerator]

theorem zero_coefficient_is_not_an_invertible_normal_coordinate :
    (¬ ∃ u : ℂˣ, (u : ℂ) = 0) ∧
    ¬ Function.Injective (fun z : ℂ ↦ sampleCenter + (0 : ℂ) * z) := by
  constructor
  · rintro ⟨u, hu⟩
    exact u.ne_zero hu
  · intro h
    have hzero : (0 : ℂ) = 1 := h (by simp)
    norm_num at hzero

theorem original_support_image_and_ordinary_point_class_are_the_same (a : ℂ) :
    schemePoint a = ProjectiveLineAffineChart.center ℂ a ∧
    pointClass a = ProjectiveLineFinitePointChow.pointClass ℂ a ∧
    ProjectiveLineCycles.rationalChowDegree ℂ (pointClass a) = 1 ∧
    pointClass a ≠ 0 := by
  refine ⟨schemePoint_eq_center a, pointClass_eq_original a, ?_, pointClass_ne_zero a⟩
  rw [pointClass_eq_original]
  exact ProjectiveLineFinitePointChow.pointClass_degree ℂ a

theorem original_point_cycle_has_the_same_geometric_gysin_unit (a : ℂ) (u : ℂˣ) :
    ProjectiveLineFinitePointGysin.gysin a u (ProjectiveLineFinitePointSupport.pointUnit a) =
      model.cycleClass (pointClass a) ∧
    h2Equiv (model.cycleClass (pointClass a)) = 1 :=
  ⟨gysin_pointUnit_eq_cycleClass a u, class_coordinate a⟩

theorem negative_point_unit_does_not_have_positive_normalization (a : ℂ) (u : ℂˣ) :
    ProjectiveLineFinitePointGysin.gysin a u (ProjectiveLineFinitePointSupport.pointUnit a) ≠ 0 ∧
    ProjectiveLineFinitePointGysin.gysin a u (-ProjectiveLineFinitePointSupport.pointUnit a) ≠
      coverGenerator := by
  constructor
  · intro h
    have hc := congrArg h2Equiv h
    rw [ProjectiveLineFinitePointGysin.gysin_pointUnit, h2Equiv_coverGenerator, map_zero] at hc
    norm_num at hc
  · intro h
    have hc := congrArg h2Equiv h
    rw [map_neg, ProjectiveLineFinitePointGysin.gysin_pointUnit,
      map_neg, h2Equiv_coverGenerator] at hc
    norm_num at hc

theorem transfer_degree_is_actual_global_rank_at_the_selected_target (a : ℂ) :
    (transfer a).degree = cover.finrank (schemePoint a) ∧
    (transfer a).degree = 2 ∧
    ∀ x : scheme, (transfer a).degree = cover.finrank x :=
  ⟨rfl, degree_eq_two a, degree_eq_geometric_rank a⟩

theorem every_finite_point_has_the_same_full_target_certificate (a : ℂ) :
    FiniteCoverageCertificate.check (certificate a) = true ∧
    (certificate a).cycles () = ProjectiveLineFinitePointChow.pointClass ℂ a ∧
    RationalHodgeConjectureAt ProjectiveLineCoverageCertificate.model :=
  ⟨accepted a, normalized_cycles a (), model_satisfies_from_finite_point a⟩

theorem nonzero_center_sample_keeps_its_actual_point_and_original_class :
    (ProjectiveLineFinitePointSupport.point sampleCenter).val = finite sampleCenter ∧
    (ProjectiveLineFinitePointSupport.point sampleCenter).val ≠ finite 0 ∧
    (certificate sampleCenter).cycles () =
      ProjectiveLineFinitePointChow.pointClass ℂ sampleCenter := by
  refine ⟨rfl, ?_, normalized_cycles sampleCenter ()⟩
  intro h
  have hc := finite_injective h
  have hr := congrArg Complex.re hc
  norm_num [sampleCenter] at hr

theorem unnormalized_push_fails_the_original_full_target_column (a : ℂ) :
    model.cycleClass (actualPush (upstairsCycles a ())) ≠
      (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i ()) : Betti) := by
  intro h
  have hc := congrArg h2Equiv h
  change h2Equiv (model.cycleClass (actualPush (actualPull (pointClass a)))) = _ at hc
  rw [geometric_chow_push_pull a, map_smul, map_smul, class_coordinate,
    degree_eq_two, target_column, h2Equiv_coverGenerator] at hc
  norm_num at hc

theorem degree_one_is_false_and_normalization_recovers_same_point (a : ℂ) :
    (¬ ∀ z : Betti, (transfer a).push ((transfer a).pull z) = (1 : ℚ) • z) ∧
    (((transfer a).degree : ℚ)⁻¹ • actualPush (actualPull (pointClass a)) = pointClass a) := by
  constructor
  · intro h
    have htwo : (transfer a).push ((transfer a).pull (model.cycleClass (pointClass a))) =
        ((transfer a).degree : ℚ) • model.cycleClass (pointClass a) := by
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (transfer a).push_comp_pull (model.cycleClass (pointClass a))
    have hc := congrArg h2Equiv (h (model.cycleClass (pointClass a)))
    rw [htwo, one_smul, map_smul, class_coordinate, degree_eq_two] at hc
    norm_num at hc
  · rw [geometric_chow_push_pull a, smul_smul, degree_eq_two]
    norm_num

theorem zero_center_gysin_unit_agrees_with_original_zero_construction (u : ℂˣ) :
    ProjectiveLineFinitePointGysin.gysin 0 u (ProjectiveLineFinitePointSupport.pointUnit 0) =
      ProjectiveLinePointGysin.gysin ProjectiveLinePointSupport.pointUnit := by
  rw [ProjectiveLineFinitePointGysin.gysin_pointUnit, ProjectiveLinePointGysin.gysin_pointUnit]

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
    `HodgeConjecture.OnePointHomotopy.continuous_map_family_of_leftInverse,
    `HodgeConjecture.OnePointHomotopy.continuous_onePointCongr_family,
    `HodgeConjecture.ProjectiveLineAffineChart.coordinateEquiv,
    `HodgeConjecture.ProjectiveLineAffineChart.coordinateEquiv_X,
    `HodgeConjecture.ProjectiveLineAffineChart.affineIso_hom,
    `HodgeConjecture.ProjectiveLineAffineChart.normalChart_opensRange,
    `HodgeConjecture.ProjectiveLineAffineChart.affineSection_normalChart,
    `HodgeConjecture.ProjectiveLineAffineChart.affineCenter_asIdeal,
    `HodgeConjecture.ProjectiveLineAffineChart.center_isClosed,
    `HodgeConjecture.ProjectiveLineAffineChart.center_ne_genericPoint,
    `HodgeConjecture.ProjectiveLineAffine.coefficient_ne_zero,
    `HodgeConjecture.ProjectiveLineAffine.inverseFamily_affineFamily,
    `HodgeConjecture.ProjectiveLineAffine.affineHomotopy,
    `HodgeConjecture.ProjectiveLineAffine.affineHomotopyFun_infinity,
    `HodgeConjecture.ProjectiveLineAffine.cohomologyPullback_affine,
    `HodgeConjecture.ProjectiveLineAffine.affineMap_finite,
    `HodgeConjecture.ProjectiveLineFinitePointSupport.preimage_complement,
    `HodgeConjecture.ProjectiveLineFinitePointSupport.complementContractibleSpace,
    `HodgeConjecture.ProjectiveLineFinitePointSupport.pointNormalHomeomorph,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.normalChartPoint_finite,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.pointSupport_scheme_base,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.normalSSetIso_inclusion,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.chartPullback_eq_original,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.chartComparison_hom,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.thomToSupportIso,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.forget_isIso,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.affineSupportedPull_thomClass,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.forget_supportedThomClass,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.gysin_pointUnit,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.gysinIso_apply,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.gysin_coordinate_independent,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.supportedGysin_coordinate_independent,
    `HodgeConjecture.ProjectiveLineFinitePointChow.pointRepresentative_val,
    `HodgeConjecture.ProjectiveLineFinitePointChow.pointClass_degree,
    `HodgeConjecture.ProjectiveLineFinitePointChow.pointClass_ne_zero,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.schemePoint_eq_center,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.pointClass_eq_original,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.gysin_pointUnit_eq_cycleClass,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.pointClass_cycleClass,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.transfer,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.degree_eq_geometric_rank,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.pull_comparison,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.push_comparison,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.upstairs_columns,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.normalized_cycles,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.accepted,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.model_satisfies_from_finite_point,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.unchanged_model_basis_source_and_original_maps,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.actual_affine_scheme_iso_keeps_original_chart_range,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.native_chart_is_the_same_actual_scheme_section,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.nontrivial_negative_and_imaginary_chart_samples,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.actual_affine_homotopy_keeps_finite_endpoints_and_infinity,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.rotated_affine_samples_act_identically_in_every_native_degree,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.actual_complement_and_normal_point_maps_agree,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.actual_singleton_unit_and_scheme_image_are_retained,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.original_relative_chart_excision_and_forget_maps_are_retained,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.actual_gysin_iso_has_positive_original_unit,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.complex_negative_and_imaginary_units_preserve_positive_orientation,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.zero_coefficient_is_not_an_invertible_normal_coordinate,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.original_support_image_and_ordinary_point_class_are_the_same,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.original_point_cycle_has_the_same_geometric_gysin_unit,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.negative_point_unit_does_not_have_positive_normalization,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.transfer_degree_is_actual_global_rank_at_the_selected_target,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.every_finite_point_has_the_same_full_target_certificate,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.nonzero_center_sample_keeps_its_actual_point_and_original_class,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.unnormalized_push_fails_the_original_full_target_column,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.degree_one_is_false_and_normalization_recovers_same_point,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.zero_center_gysin_unit_agrees_with_original_zero_construction]
  unless declarations.length = 68 do
    throwError "Expected exactly 68 finite-point Gysin audit declarations"
  for declaration in declarations do
    unless env.contains declaration do
      throwError "Missing finite-point Gysin audit declaration {declaration}"
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
  let coreEndpoints := [
    `HodgeConjecture.ProjectiveLineFinitePointGysin.gysin_pointUnit,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.supportedGysin_coordinate_independent]
  unless forbiddenCoreModules.length = 6 ∧ coreEndpoints.length = 2 do
    throwError "Expected six forbidden core origins and two native Gysin endpoints"
  for endpoint in coreEndpoints do
    unless env.contains endpoint do
      throwError "Missing finite-point core endpoint {endpoint}"
    let closure ← match projectDependencies env endpoint with
      | .ok closure => pure closure
      | .error message => throwError "{message}"
    let forbiddenUses := closure.toList.filter fun name ↦
      match env.getModuleIdxFor? name with
      | some idx =>
          let origin := env.header.moduleNames[idx]!
          forbiddenCoreModules.contains origin ||
            (`HodgeConjecture.Realization.Chow).isPrefixOf origin ||
            (`HodgeConjecture.Realization.DeRham).isPrefixOf origin
      | none => false
    unless forbiddenUses.isEmpty do
      throwError "Old square/ramification or realization layer entered native core {endpoint}: {forbiddenUses}"
    logInfo m!"PASS independent affine finite-point Gysin core: {endpoint}"
  let forbiddenOldResults := [
    `HodgeConjecture.ProjectiveLineSquarePullback.cohomologyPullback_square,
    `HodgeConjecture.ProjectiveLineSquarePullback.cohomologyPullback_square_eq,
    `HodgeConjecture.ProjectiveLineSquarePullback.canonical_cohomologyPullback_square]
  let forbiddenFinalModules := [
    `HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage,
    `HodgeConjecture.Realization.DeRham.ProjectiveLineRamificationComparison]
  unless forbiddenOldResults.length = 3 ∧ forbiddenFinalModules.length = 2 do
    throwError "Expected three old global results and both old fixture origins"
  for name in forbiddenOldResults ++
      [`HodgeConjecture.ProjectiveLineSquareCoverage.model_satisfies_from_square_cover,
       `HodgeConjecture.ProjectiveLineRamificationComparison.model_satisfies_from_ramification] do
    unless env.contains name do
      throwError "Missing old-result witness for finite-point dependency guard {name}"
  let finalEndpoint :=
    `HodgeConjecture.ProjectiveLineFinitePointComparison.model_satisfies_from_finite_point
  unless env.contains finalEndpoint do
    throwError "Missing finite-point family endpoint {finalEndpoint}"
  let finalClosure ← match projectDependencies env finalEndpoint with
    | .ok closure => pure closure
    | .error message => throwError "{message}"
  for name in forbiddenOldResults do
    if finalClosure.contains name then
      throwError "Old absolute square proof {name} entered finite-point endpoint"
  let oldFixtureUses := finalClosure.toList.filter fun name ↦
    match env.getModuleIdxFor? name with
    | some idx => forbiddenFinalModules.contains env.header.moduleNames[idx]!
    | none => false
  unless oldFixtureUses.isEmpty do
    throwError "Old fixture declarations entered finite-point family: {oldFixtureUses}"
  logInfo m!"PASS independent finite-point family endpoint: {finalEndpoint}"
  let required := [
    `HodgeConjecture.ProjectiveLineFinitePointGysin.pointSupport_scheme_base,
    `HodgeConjecture.ProjectiveLineAffineChart.affineSection_normalChart,
    `HodgeConjecture.OnePointHomotopy.continuous_map_family_of_leftInverse,
    `HodgeConjecture.ProjectiveLineAffine.affineHomotopy,
    `HodgeConjecture.ProjectiveLineAffine.cohomologyPullback_affine,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.gysin_pointUnit,
    `HodgeConjecture.ProjectiveLineSquare.square_finrank]
  unless required.length = 7 do
    throwError "Expected seven actual support/chart/homotopy/Gysin/global-rank dependencies"
  for name in required do
    unless env.contains name do
      throwError "Missing finite-point required dependency {name}"
    unless finalClosure.contains name do
      throwError "Required actual finite-point dependency {name} missing from {finalEndpoint}"
    logInfo m!"PASS required finite-point dependency: {name}"

end HodgeConjecture.ProjectiveLineFinitePointGysinVerification

end
