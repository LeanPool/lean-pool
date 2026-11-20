/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.SeedParameters
public import LeanPool.FastDynamo.Local.ModifiedBessel
public import LeanPool.FastDynamo.Local.ModifiedBesselIRecurrence
public import LeanPool.FastDynamo.Local.ModifiedBesselK
public import LeanPool.FastDynamo.Local.ModifiedBesselKAnalytic
public import LeanPool.FastDynamo.Local.ModifiedBesselKRecurrence
public import LeanPool.FastDynamo.Global.ScaleSelection
public import LeanPool.FastDynamo.Global.BackgroundMultiplierScalarAlgebra
public import LeanPool.FastDynamo.Fourier.AxialL2
public import LeanPool.FastDynamo.Fourier.PeriodicH2
public import LeanPool.FastDynamo.Fourier.PeriodicH2AxialSector
public import LeanPool.FastDynamo.Fourier.ProductH2
public import LeanPool.FastDynamo.Analysis.PeriodicWeakDerivative
public import LeanPool.FastDynamo.Analysis.PeriodicWeakDerivativeTest
public import LeanPool.FastDynamo.Analysis.Holder
public import LeanPool.FastDynamo.Analysis.TransverseVecMultipliers
public import LeanPool.FastDynamo.Analysis.TransverseVecMultiplierAlgebra
public import LeanPool.FastDynamo.Analysis.TransverseWeightedDiffusion
public import LeanPool.FastDynamo.Analysis.TorusHaarTransport
public import LeanPool.FastDynamo.Analysis.ProductFourier
public import LeanPool.FastDynamo.Analysis.ProductWeakDerivative
public import LeanPool.FastDynamo.Analysis.ProductScalarEnergy
public import LeanPool.FastDynamo.Analysis.ProductVectorCalculus
public import LeanPool.FastDynamo.Analysis.ProductDivergenceEnergy
public import LeanPool.FastDynamo.Analysis.WeakLeibniz
public import LeanPool.FastDynamo.Analysis.WeakLeibnizAxial
public import LeanPool.FastDynamo.Analysis.WeakLeibnizVelocity
public import LeanPool.FastDynamo.Analysis.TransverseWeightedLeibniz
public import LeanPool.FastDynamo.Analysis.TransverseVecCutoffMultiplier
public import LeanPool.FastDynamo.Analysis.ProductTransportEnergy
public import LeanPool.FastDynamo.Analysis.InductionDivergence
public import LeanPool.FastDynamo.Analysis.TransverseW1Inf
public import LeanPool.FastDynamo.Analysis.TransverseChart
public import LeanPool.FastDynamo.Analysis.PlaneJacobian
public import LeanPool.FastDynamo.Analysis.R3Assembly
public import LeanPool.FastDynamo.Analysis.R3BlockComplexify
public import LeanPool.FastDynamo.Analysis.Realification
public import LeanPool.FastDynamo.Analysis.WholePlaneFourier
public import LeanPool.FastDynamo.Analysis.ScalarSecondPartial
public import LeanPool.FastDynamo.Analysis.ScalarSecondPartialBridges
public import LeanPool.FastDynamo.Analysis.WholePlaneH2
public import LeanPool.FastDynamo.Analysis.WholePlaneSobolev
public import LeanPool.FastDynamo.Analysis.WholePlaneH1Core
public import LeanPool.FastDynamo.Analysis.WholePlaneIntegralWeakDerivative
public import LeanPool.FastDynamo.Analysis.WholePlaneUnitCircleSurface
public import LeanPool.FastDynamo.Analysis.WholePlaneRadialExponential
public import LeanPool.FastDynamo.Analysis.WholePlanePiecewiseSliceIBP
public import LeanPool.FastDynamo.Analysis.WholePlaneUnitCircleSlices
public import LeanPool.FastDynamo.Analysis.WholePlaneSliceProductRule
public import LeanPool.FastDynamo.Analysis.WholePlaneTwoJumpIntegrationByParts
public import LeanPool.FastDynamo.Analysis.WholePlaneUnitDiskSliceGeometry
public import LeanPool.FastDynamo.Analysis.WholePlaneUnitCircleWeightedSlices
public import LeanPool.FastDynamo.Analysis.WholePlaneUnitDiskFibreDerivativeSource
public import LeanPool.FastDynamo.Analysis.WholePlaneUnitDiskFibreBranches
public import LeanPool.FastDynamo.Analysis.AntiDual
public import LeanPool.FastDynamo.Analysis.WholePlaneH1AntiDual
public import LeanPool.FastDynamo.Analysis.ComplexForm
public import LeanPool.FastDynamo.Analysis.AnalyticOperatorHelpers
public import LeanPool.FastDynamo.Analysis.WholePlaneScaling
public import LeanPool.FastDynamo.Analysis.WholePlaneCoefficientScaling
public import LeanPool.FastDynamo.Analysis.WholePlaneCoefficientScalingCoordinateCompatibility
public import LeanPool.FastDynamo.Analysis.WholePlaneLInfTempered
public import LeanPool.FastDynamo.Analysis.WholePlaneScalarLeibniz
public import LeanPool.FastDynamo.Analysis.WholePlaneCoordinateDistributions
public import LeanPool.FastDynamo.Analysis.BoundedOperatorMultiplier
public import LeanPool.FastDynamo.Analysis.WholePlaneBesselWeight
public import LeanPool.FastDynamo.Analysis.FourierMultiplierSub
public import LeanPool.FastDynamo.Analysis.WholePlaneCoordinateH1
public import LeanPool.FastDynamo.Analysis.WholePlaneH1L4Embedding
public import LeanPool.FastDynamo.Analysis.WholePlaneL4FormPerturbationHolder
public import LeanPool.FastDynamo.Analysis.WholePlaneLocalCompactness
public import LeanPool.FastDynamo.Analysis.WholePlaneBandLimitedCompactness
public import LeanPool.FastDynamo.Analysis.WholePlaneBandLimitedRellich
public import LeanPool.FastDynamo.Analysis.WholePlaneBandLimitedRellichUnconditional
public import LeanPool.FastDynamo.Analysis.WholePlaneLocalCompactnessUnconditional
public import LeanPool.FastDynamo.Operator.WholePlanePivotAntiDual
public import LeanPool.FastDynamo.Operator.FixedSector
public import LeanPool.FastDynamo.Operator.WholePlaneLocal
public import LeanPool.FastDynamo.Local.RadialVelocity
public import LeanPool.FastDynamo.Local.PonomarenkoDispersionAnalytic
public import LeanPool.FastDynamo.Local.ModifiedBesselWronskian
public import LeanPool.FastDynamo.Local.ModifiedBesselIIntegral
public import LeanPool.FastDynamo.Local.ModifiedBesselKGaussian
public import LeanPool.FastDynamo.Local.ModifiedBesselIGaussian
public import LeanPool.FastDynamo.Local.ModifiedBesselGaussianMoments
public import LeanPool.FastDynamo.Local.PonomarenkoOrderOneProduct
public import LeanPool.FastDynamo.Local.PonomarenkoGaussianFactors
public import LeanPool.FastDynamo.Local.PonomarenkoCrossNormalizedJump
public import LeanPool.FastDynamo.Local.ModifiedBesselKODE
public import LeanPool.FastDynamo.Local.PonomarenkoCrossNormalizedAxial
public import LeanPool.FastDynamo.Local.ModifiedBesselBoundaryBehavior
public import LeanPool.FastDynamo.Local.PonomarenkoFreeOmegaInterface
public import LeanPool.FastDynamo.Local.PonomarenkoRealRadialBridge
public import LeanPool.FastDynamo.Local.PonomarenkoCrossNormalizedRadialODE
public import LeanPool.FastDynamo.Local.PonomarenkoOriginProfiles
public import LeanPool.FastDynamo.Local.ComplexRadius
public import LeanPool.FastDynamo.Local.PonomarenkoCartesianInteriorDerivative
public import LeanPool.FastDynamo.Local.PonomarenkoCartesianExteriorDerivative
public import LeanPool.FastDynamo.Local.PonomarenkoCartesianExteriorPhysicalDerivative
public import LeanPool.FastDynamo.Local.PonomarenkoCartesianExteriorDecay
public import LeanPool.FastDynamo.Local.WholePlaneSliceRadius
public import LeanPool.FastDynamo.Local.PonomarenkoExteriorDerivativeDecay
public import LeanPool.FastDynamo.Local.PonomarenkoExteriorSecondDerivative
public import LeanPool.FastDynamo.Local.PolarHessianCalculus
public import LeanPool.FastDynamo.Local.PonomarenkoExteriorSecondPartialBounds
public import LeanPool.FastDynamo.Local.PonomarenkoCartesianPolarLaplacian
public import LeanPool.FastDynamo.Local.ParameterizedRadialSmoothing
public import LeanPool.FastDynamo.Operator.AssociatedForm
public import LeanPool.FastDynamo.Operator.ComplexFormAntiDual
public import LeanPool.FastDynamo.Operator.ScalarCoefficientPivot
public import LeanPool.FastDynamo.Operator.CompactAdjoint
public import LeanPool.FastDynamo.Operator.CompactOperatorSum
public import LeanPool.FastDynamo.Operator.FormCoercivityConstants
public import LeanPool.FastDynamo.Operator.Contour
public import LeanPool.FastDynamo.Operator.Riesz
public import LeanPool.FastDynamo.Operator.RieszDomainCalculus
public import LeanPool.FastDynamo.Operator.RieszResolventIdentity
public import LeanPool.FastDynamo.Operator.ResolventHolomorphy
public import LeanPool.FastDynamo.Operator.ResolventPropagation
public import LeanPool.FastDynamo.Operator.FixedSectorBasic
public import LeanPool.FastDynamo.Operator.PointwiseResolvent
public import LeanPool.FastDynamo.Operator.RieszProjectionCalculus
public import LeanPool.FastDynamo.Operator.FredholmIsolation
public import LeanPool.FastDynamo.Operator.AnalyticFredholm
public import LeanPool.FastDynamo.Operator.DomainPencilFredholm
public import LeanPool.FastDynamo.Operator.Product
public import LeanPool.FastDynamo.Operator.Compatibility
public import LeanPool.FastDynamo.Operator.Evolution
public import LeanPool.FastDynamo.Operator.RealCompatibility
public import LeanPool.FastDynamo.Finish.NegativeDiffusivity
public import LeanPool.FastDynamo.Finish.RealSolution
public import LeanPool.FastDynamo.Reduction.ExactScalingParameters
public import LeanPool.FastDynamo.Reduction.ExactScalingC2
public import LeanPool.FastDynamo.Operator.FiniteDimensionalDeterminant
public import LeanPool.FastDynamo.Analysis.WholePlaneExteriorCutoff
public import LeanPool.FastDynamo.Analysis.TransverseLocalizedNorm
public import LeanPool.FastDynamo.Operator.FixedSectorResolvent
public import LeanPool.FastDynamo.Local.HelicalProfile
public import LeanPool.FastDynamo.Global.CellGeometry
public import LeanPool.FastDynamo.Local.ParameterizedHelicalProfile
public import LeanPool.FastDynamo.Operator.FixedSectorDiffusionInverse
public import LeanPool.FastDynamo.Operator.FixedSectorLowerOrderDecay
public import LeanPool.FastDynamo.Operator.HorizontalProjection
public import LeanPool.FastDynamo.Operator.HorizontalSector
public import LeanPool.FastDynamo.Operator.VerticalZeroExtend
public import LeanPool.FastDynamo.Operator.WholePlaneLocalC2
public import LeanPool.FastDynamo.Global.TorusCellPlacement
public import LeanPool.FastDynamo.Global.TorusChartEmbedding
public import LeanPool.FastDynamo.Global.TorusChartL2Operators
public import LeanPool.FastDynamo.Global.TorusIocFundamentalBox
public import LeanPool.FastDynamo.Global.TorusChartH2Transfer
public import LeanPool.FastDynamo.Global.CellSeriesSummability
public import LeanPool.FastDynamo.Operator.CompactAtkinson
public import LeanPool.FastDynamo.Operator.CompactAtkinsonIndexZero
public import LeanPool.FastDynamo.Operator.ResolventAnnulus
public import LeanPool.FastDynamo.Operator.AnalyticFredholmContinuation
public import LeanPool.FastDynamo.Global.TorusHelicalSource
public import LeanPool.FastDynamo.Global.TorusChartWeakTransfer
public import LeanPool.FastDynamo.Global.ConstantCoefficientWeakForm
public import LeanPool.FastDynamo.Global.TorusChartFourierWeakTransfer
public import LeanPool.FastDynamo.Analysis.BumpAffineScaling
public import LeanPool.FastDynamo.Global.WholePlaneW1InfCertificates
public import LeanPool.FastDynamo.Global.TransverseCoefficientMultipliers
public import LeanPool.FastDynamo.Global.TorusLocalCoreMeasurability
public import LeanPool.FastDynamo.Analysis.WholePlaneScalarH2Leibniz
public import LeanPool.FastDynamo.Global.TorusVelocityConcrete
public import LeanPool.FastDynamo.Global.MatchingCellScalingParameters
public import LeanPool.FastDynamo.Global.TorusAxialVelocityChartFields
public import LeanPool.FastDynamo.Global.TorusAxialVelocityConcrete
public import LeanPool.FastDynamo.Global.TorusAxialPlateauRadial
public import LeanPool.FastDynamo.Global.TorusAxialVelocityWeakTransfer
public import LeanPool.FastDynamo.Global.TorusFullVelocityConcrete
public import LeanPool.FastDynamo.Global.FrequencyRatioDichotomy
public import LeanPool.FastDynamo.Global.DomainOperatorNumericalRange
public import LeanPool.FastDynamo.Operator.DomainOperatorClosedRangeAdjoint
public import LeanPool.FastDynamo.Global.ReducedInductionEnergyIdentity
public import LeanPool.FastDynamo.Global.ReducedInductionAdjoint
public import LeanPool.FastDynamo.Global.ReducedInductionHalfPlaneResolvent
public import LeanPool.FastDynamo.Global.ParametrixExplicitCutoffDerivatives
public import LeanPool.FastDynamo.Global.ParametrixNeumannCorrection
public import LeanPool.FastDynamo.Global.LocalizedSummandAlgebra
public import LeanPool.FastDynamo.Global.PeriodicSecondOrderCutoffs
public import LeanPool.FastDynamo.Analysis.TransverseSmoothH2CutoffMultiplier
public import LeanPool.FastDynamo.Analysis.TransverseSmoothBumpH2CutoffConcrete
public import LeanPool.FastDynamo.Analysis.TransverseSmoothBumpPeriodization
public import LeanPool.FastDynamo.Global.CorrectedRieszProjectionEigenmode
public import LeanPool.FastDynamo.Global.ConstantCoefficientBackgroundResolvent
public import LeanPool.FastDynamo.Global.WholePlaneEllipticRegularity
public import LeanPool.FastDynamo.Operator.RieszSpectralMomentCalculus
public import LeanPool.FastDynamo.Operator.RieszEigenvalueLocalization
public import LeanPool.FastDynamo.Operator.AdjointRealizationFromResolvent
public import LeanPool.FastDynamo.Analysis.ProductH2DenseEmbedding
public import LeanPool.FastDynamo.Analysis.WholePlaneH2DenseEmbedding
public import LeanPool.FastDynamo.Global.CorrectedRieszProjectionSpectralCalculus
public import LeanPool.FastDynamo.Global.TorusSupportedH2Output
public import LeanPool.FastDynamo.Local.ModifiedBesselHigherGaussianMoments
public import LeanPool.FastDynamo.Local.ModifiedBesselKSecondOrderGaussian
public import LeanPool.FastDynamo.Local.PonomarenkoSecondOrderProduct
public import LeanPool.FastDynamo.Local.PonomarenkoSectorOrderOneProduct
public import LeanPool.FastDynamo.Local.PonomarenkoSegmentDispersion
public import LeanPool.FastDynamo.Local.PonomarenkoSegmentRoot
public import LeanPool.FastDynamo.Local.WholePlaneC2
public import LeanPool.FastDynamo.Local.HorizontalWeakForm
public import LeanPool.FastDynamo.Local.HorizontalFormOperator
public import LeanPool.FastDynamo.Local.HorizontalFormCompactness
public import LeanPool.FastDynamo.Local.HorizontalModeBranches
public import LeanPool.FastDynamo.Local.HorizontalModeH1
public import LeanPool.FastDynamo.Local.HorizontalModeWeakIdentity
public import LeanPool.FastDynamo.Local.HorizontalModeSurface
public import LeanPool.FastDynamo.Local.HorizontalModeSecondDerivatives
public import LeanPool.FastDynamo.Local.HorizontalModeExteriorSecondDerivatives
public import LeanPool.FastDynamo.Local.HorizontalModeBulkIdentity
public import LeanPool.FastDynamo.Local.HorizontalModeBulkL2
public import LeanPool.FastDynamo.Local.HorizontalModeInterface
public import LeanPool.FastDynamo.Local.HorizontalModeEigenpair
public import LeanPool.FastDynamo.Local.HorizontalModeIsolation
public import LeanPool.FastDynamo.Local.HorizontalFormResolvent
public import LeanPool.FastDynamo.Local.HorizontalModeContour
public import LeanPool.FastDynamo.Local.HorizontalFormDelta
public import LeanPool.FastDynamo.Local.HorizontalSmoothedVelocity
public import LeanPool.FastDynamo.Local.HorizontalFormPerturbation
public import LeanPool.FastDynamo.Local.HorizontalFormSmallness
public import LeanPool.FastDynamo.Local.HorizontalFormNeumann
public import LeanPool.FastDynamo.Local.HorizontalDeltaResolvent
public import LeanPool.FastDynamo.Local.HorizontalRieszPerturbation
public import LeanPool.FastDynamo.Local.HorizontalFormStrongIdentification
public import LeanPool.FastDynamo.Local.HorizontalSeedResolventH2
public import LeanPool.FastDynamo.Local.HorizontalSeedWitness
public import LeanPool.FastDynamo.Local.HorizontalSeedUniformResolvent
public import LeanPool.FastDynamo.Finish.MagneticScale
public import LeanPool.FastDynamo.Finish.GrowingModeEvolution
public import LeanPool.FastDynamo.Dynamics.StronglyContinuousSemigroup
public import LeanPool.FastDynamo.Dynamics.StrongSolutionUniqueness
public import LeanPool.FastDynamo.Dynamics.GrowthBound
public import LeanPool.FastDynamo.Dynamics.SemigroupRestriction
public import LeanPool.FastDynamo.Dynamics.GrowthBoundLimit
public import LeanPool.FastDynamo.Dynamics.HilleYosida.OperatorExp
public import LeanPool.FastDynamo.Dynamics.HilleYosida.ResolventRay
public import LeanPool.FastDynamo.Dynamics.HilleYosida.YosidaApproximant
public import LeanPool.FastDynamo.Dynamics.HilleYosida.ApproximantSemigroup
public import LeanPool.FastDynamo.Dynamics.HilleYosida.Convergence
public import LeanPool.FastDynamo.Dynamics.HilleYosida.Semigroup
public import LeanPool.FastDynamo.Dynamics.HilleYosida.Invariance
public import LeanPool.FastDynamo.Dynamics.HilleYosida.Realization
public import LeanPool.FastDynamo.Dynamics.HilleYosida.Generation
public import LeanPool.FastDynamo.Dynamics.Assembly.AxialHilbertSum
public import LeanPool.FastDynamo.Dynamics.Assembly.AxialSectorDomain
public import LeanPool.FastDynamo.Dynamics.Assembly.UniformSectorResolvent
public import LeanPool.FastDynamo.Dynamics.Assembly.SolenoidalSubspace
public import LeanPool.FastDynamo.Dynamics.Assembly.ProductResolvent
public import LeanPool.FastDynamo.Dynamics.Assembly.ProductSemigroup
public import LeanPool.FastDynamo.Dynamics.Assembly.SemigroupOrbit
public import LeanPool.FastDynamo.Dynamics.Assembly.MainGrowthRate
public import LeanPool.FastDynamo.Dynamics.Assembly.MainGrowthRateLimit
public import LeanPool.FastDynamo.Dynamics.MainGrowthFloor
public import LeanPool.FastDynamo.Dynamics.Flow.LipschitzRate
public import LeanPool.FastDynamo.Dynamics.ParticleFlow
public import LeanPool.FastDynamo.Dynamics.Flow.RadialShear
public import LeanPool.FastDynamo.Dynamics.Flow.CellProfiles
public import LeanPool.FastDynamo.Dynamics.Flow.CellFlowMap
public import LeanPool.FastDynamo.Dynamics.Flow.PlaneFlow
public import LeanPool.FastDynamo.Dynamics.Flow.PlaneFlowRegularity
public import LeanPool.FastDynamo.Dynamics.Flow.PlaneFlowLipschitz
public import LeanPool.FastDynamo.Dynamics.Flow.PeriodizedFlowData
public import LeanPool.FastDynamo.Dynamics.Flow.PeriodizedFlowSymbol
public import LeanPool.FastDynamo.Dynamics.Flow.TorusFlow
public import LeanPool.FastDynamo.Dynamics.Flow.Entropy
public import LeanPool.FastDynamo.Dynamics.Flow.FlowDerivative
public import LeanPool.FastDynamo.Dynamics.Flow.MeasurePreserving
public import LeanPool.FastDynamo.Dynamics.Flow.ParticleFlowProof
public import LeanPool.FastDynamo.Dynamics.Flow.ParticleFlowUniqueness
public import LeanPool.FastDynamo.Dynamics.Ideal.CauchyOperator
public import LeanPool.FastDynamo.Dynamics.Ideal.GradientOrthogonality
public import LeanPool.FastDynamo.Dynamics.Ideal.TruncatedPlaneFlow
public import LeanPool.FastDynamo.Dynamics.Ideal.TruncatedFlow
public import LeanPool.FastDynamo.Dynamics.Ideal.TruncatedTransport
public import LeanPool.FastDynamo.Dynamics.Ideal.TruncatedConvergence
public import LeanPool.FastDynamo.Dynamics.Ideal.SolenoidalInvariance
public import LeanPool.FastDynamo.Dynamics.Ideal.StrongContinuity
public import LeanPool.FastDynamo.Dynamics.Ideal.IdealGroup
public import LeanPool.FastDynamo.Dynamics.ReducedInductionHilleYosidaRay
public import LeanPool.FastDynamo.Global.WholePlaneAESupport
public import LeanPool.FastDynamo.Global.TorusCellSeedCoefficientBridge
public import LeanPool.FastDynamo.Global.TorusCellAxialPlateauBridge
public import LeanPool.FastDynamo.Global.TorusChartMultiplierDescent
public import LeanPool.FastDynamo.Global.WholePlaneCutoffCommutator
public import LeanPool.FastDynamo.Operator.CompactBaseInjectiveResolvent
public import LeanPool.FastDynamo.Global.TorusGlobalVelocityQualitative
public import LeanPool.FastDynamo.Main
public import LeanPool.FastDynamo.Operator.CompactBaseFredholm
public import LeanPool.FastDynamo.Operator.HorizontalSectorBasic
public import LeanPool.FastDynamo.Finish.AxialRecoveryDivergence
public import LeanPool.FastDynamo.Finish.AxialRecoveryRegularity
public import LeanPool.FastDynamo.Finish.AxialRecovery
public import LeanPool.FastDynamo.Global.HorizontalTransportSkewness
public import LeanPool.FastDynamo.Global.TorusBackgroundWeightedEnergy
public import LeanPool.FastDynamo.Global.TorusBackgroundVelocity
public import LeanPool.FastDynamo.Global.TorusBackgroundMultiplierCell
public import LeanPool.FastDynamo.Global.TorusBackgroundMultiplier
public import LeanPool.FastDynamo.Global.TorusBackgroundParameters
public import LeanPool.FastDynamo.Global.TorusBackgroundResolvent
public import LeanPool.FastDynamo.Global.WholePlaneScaledLocalResolvent
public import LeanPool.FastDynamo.Global.SpectralCircleGrowthFloor
public import LeanPool.FastDynamo.Global.HorizontalSpectralExtraction
public import LeanPool.FastDynamo.Global.ParametrixCutoffs
public import LeanPool.FastDynamo.Global.HorizontalCutoffCommutator
public import LeanPool.FastDynamo.Global.TorusTwoSummandParametrix
public import LeanPool.FastDynamo.Global.TorusParametrixError
public import LeanPool.FastDynamo.Global.TorusSchwartzPeriodicCutoff
public import LeanPool.FastDynamo.Global.HorizontalCutoffMultiplier
public import LeanPool.FastDynamo.Global.TorusPlacedCutoffC2
public import LeanPool.FastDynamo.Global.TorusPlacedCutoffVelocity
public import LeanPool.FastDynamo.Global.TorusCellPlacedCutoffs
public import LeanPool.FastDynamo.Global.TorusBackgroundParametrixBridge
public import LeanPool.FastDynamo.Global.WholePlaneHorizontalFibre
public import LeanPool.FastDynamo.Global.TorusChartC2Transfer
public import LeanPool.FastDynamo.Global.TorusChartProjectionTransport
public import LeanPool.FastDynamo.Global.TorusChartActionBridge
public import LeanPool.FastDynamo.Global.TorusChartCutoffSupport
public import LeanPool.FastDynamo.Global.TorusChartC2AuxiliaryCutoff
public import LeanPool.FastDynamo.Global.TorusChartC2TransportedField
public import LeanPool.FastDynamo.Global.TorusChartC2TransportedBounds
public import LeanPool.FastDynamo.Global.TorusSelectedLocalResolventData
public import LeanPool.FastDynamo.Global.TorusSelectedCellParametrixData
public import LeanPool.FastDynamo.Global.TorusSelectedWitness
public import LeanPool.FastDynamo.Global.TorusSelectedContourIdentity
public import LeanPool.FastDynamo.Global.TorusGlobalRieszNonzero
public import LeanPool.FastDynamo.Global.TorusGlobalSpectralTransfer
public import LeanPool.FastDynamo.Operator.ReducedInductionScaling
public import LeanPool.FastDynamo.Global.TorusGlobalVelocityRegularity
public import LeanPool.FastDynamo.Global.PairChartRotation
public import LeanPool.FastDynamo.Global.TorusGlobalVelocityLipschitz
public import LeanPool.FastDynamo.Global.GlobalParameterChoice
public import LeanPool.FastDynamo.Local.LocalSeedC2
public import LeanPool.FastDynamo.Local.LocalSeedC2Concrete
public import LeanPool.FastDynamo.Global.TorusSelectedCellVelocityFacts
public import LeanPool.FastDynamo.Global.TorusSelectedCellChartAgreement
public import LeanPool.FastDynamo.Global.GlobalParameterChoiceConcrete
public import LeanPool.FastDynamo.Global.ParameterChainWitnesses
public import LeanPool.FastDynamo.Global.GlobalSpectralTransferConcrete
public import LeanPool.FastDynamo.Global.MainTheoremWitnesses
public import LeanPool.FastDynamo.MainTheorem
public import LeanPool.FastDynamo.Global.GlobalSpectralTransferAllCells
public import LeanPool.FastDynamo.Analysis.LiteralThreeTorus
public import LeanPool.FastDynamo.Analysis.TorusNet
public import LeanPool.FastDynamo.Analysis.EntropyCriterion
public import LeanPool.FastDynamo.Analysis.LiteralTorusRepresentative
public import LeanPool.FastDynamo.Analysis.LiteralThreeTorusGradient
public import LeanPool.FastDynamo.Analysis.LpCompMeasurePreserving
public import LeanPool.FastDynamo.Analysis.LogLinearGrowth
public import LeanPool.FastDynamo.Global.TransverseFundamentalBox
public import LeanPool.FastDynamo.MainTheoremStrengthened
public import LeanPool.FastDynamo.Dynamics.MainLagrangianClauses
public import LeanPool.FastDynamo.Dynamics.Assembly.FastDynamo
public import LeanPool.FastDynamo.Dynamics.Assembly.NormalizedGrowthRate
public import LeanPool.FastDynamo.Dynamics.EnergyIdentity
public import LeanPool.FastDynamo.Dynamics.NormalizedLagrangianClauses
public import LeanPool.FastDynamo.Dynamics.SemigroupTimeRescaling
public import LeanPool.FastDynamo.Finish.MagneticScaleMain
public import LeanPool.FastDynamo.Finish.RealPartNotEigenmode
public import LeanPool.FastDynamo.Finish.ZeroMean
public import LeanPool.FastDynamo.Global.TorusBackgroundResolventHolomorphic
public import LeanPool.FastDynamo.Local.HorizontalSpectrumEigenvalue
public import LeanPool.FastDynamo.MainTheoremNormalized
public import LeanPool.FastDynamo.Operator.ResolventSetHolomorphy
public import LeanPool.FastDynamo.Dynamics.Assembly.ProductInductionEnergy
public import LeanPool.FastDynamo.Dynamics.Ideal.VelocityGradient
public import LeanPool.FastDynamo.Dynamics.IdealWeakForm
public import LeanPool.FastDynamo.Dynamics.IdealWeakFormRescaling
public import LeanPool.FastDynamo.Dynamics.SemigroupGenerator
public import LeanPool.FastDynamo.Global.TorusGlobalVelocityDerivativeBridge
public import LeanPool.FastDynamo.Operator.StrongHolomorphy
public import LeanPool.FastDynamo.Operator.UnboundedResolvent
public import LeanPool.FastDynamo.Analysis.LiteralTorusMollifier
public import LeanPool.FastDynamo.Dynamics.AnalyticSemigroup
public import LeanPool.FastDynamo.Dynamics.Assembly.InductionMeanConservation
public import LeanPool.FastDynamo.Dynamics.Assembly.SolenoidalGenerator
public import LeanPool.FastDynamo.Dynamics.Flow.VariationalEquation
public import LeanPool.FastDynamo.Dynamics.HilleYosida.AnalyticGeneration
public import LeanPool.FastDynamo.Dynamics.HilleYosida.GeneratorIdentification
public import LeanPool.FastDynamo.Operator.ProductH2Compact
public import LeanPool.FastDynamo.Dynamics.AnalyticSemigroupGenerator
public import LeanPool.FastDynamo.Dynamics.Assembly.NegativeSobolevResolvent
public import LeanPool.FastDynamo.Dynamics.Assembly.PhysicalInductionUniqueness
public import LeanPool.FastDynamo.Dynamics.Ideal.LipschitzTestFields
public import LeanPool.FastDynamo.Dynamics.Ideal.WeakSolution
public import LeanPool.FastDynamo.Analysis.LiteralFriedrichsCommutator
public import LeanPool.FastDynamo.Dynamics.SemigroupSpectralMapping
public import LeanPool.FastDynamo.Dynamics.Assembly.InductionSemigroupSpectrum
public import LeanPool.FastDynamo.Dynamics.Ideal.WeakSolutionUniqueness
public import LeanPool.FastDynamo.Dynamics.VanishingDiffusivity.ProductBridge
public import LeanPool.FastDynamo.Dynamics.VanishingDiffusivity.Limit
public import LeanPool.FastDynamo.Dynamics.Assembly.SemigroupSpectralGrowth
public import LeanPool.FastDynamo.Palomar.Statement
public import LeanPool.FastDynamo.Palomar.FourierDictionary
public import LeanPool.FastDynamo.Palomar.Solenoidal
public import LeanPool.FastDynamo.Palomar.H2Dictionary
public import LeanPool.FastDynamo.Palomar.InductionSymbol
public import LeanPool.FastDynamo.Palomar.Velocity
public import LeanPool.FastDynamo.Palomar.Flow
public import LeanPool.FastDynamo.Palomar.SemigroupEigenmode
public import LeanPool.FastDynamo.Palomar.InductionSemigroup
public import LeanPool.FastDynamo.Palomar.Eigenmode
public import LeanPool.FastDynamo.Palomar.IdealSymbol
public import LeanPool.FastDynamo.Palomar.IdealGroup
public import LeanPool.FastDynamo.Palomar.IdealUniqueness
public import LeanPool.FastDynamo.Palomar.Main

/-!
# A fast dynamo with zero topological entropy

Source: arxiv:2608.02586v3, url:https://github.com/lukasniebel/fast_dynamo_lean/tree/f2e17cdd0f814af1bd9c0a6ce10320b216ed4fe0
Authors: Lukas Niebel
Status: verified
Main declarations: `FastDynamo.challenge_statement`, `FastDynamo.main_theorem_strengthened`,
  `FastDynamo.tendstoUniformlyOn_resistiveEvolution_mainIdealGroup`
Tags: kinematic-dynamo, induction-equation, spectral-theory, topological-entropy
MSC: 35Q35, 76W05, 37B40
-/

/-!
# Fast dynamo: root module

This library formalises the paper *A fast dynamo with zero topological entropy*
(L. Niebel, arXiv:2608.02586v3): both halves of Theorem 1.2 (`thm:main`), the spectral one and
the dynamical one, together with the results around it — Lemma A.1
(`lem:semigroup-spectral-growth`), `prop:particle-flow`, `cor:ideal-growth` with the weak
form of the ideal induction equation, `cor:magnetic-scale` at the theorem's witnesses, and
the assertions of Remarks 1.4–1.7.  The release surface is:

* `FastDynamo.Main`: the statement `MainPhysicalConclusion` (the theorem's "More
  precisely" clause and its real-datum clause, without the semigroup growth-rate clause)
  and its reduction to the reduced-operator target `MainReducedTarget`.
* `FastDynamo.MainTheorem`: the proofs `mainPhysicalConclusion_holds`
  and `mainReducedTarget_holds`.
* `FastDynamo.MainTheoremStrengthened`: the stronger form the proof delivers,
  `main_theorem_strengthened` — explicit witnesses `mainVelocity`, `mainEps0`,
  `mainGrowthFloor` with `γ₀ = g_* ≥ (3/4)(448 − 4π²) ≥ 288`, Proposition 7.1 at
  every admissible cell, the normalised velocity, the qualitative regularity of the
  velocity's chart-side and periodised representatives, the magnetic clauses on the
  literal `Torus 3`, the growth-rate clause `γ(u, ε) ≥ γ₀` for `0 < ε ≤ ε₀`, and
  `eq:main-thm-growth` for the semigroup orbit of the real datum and for every solution of the
  curl-form equation with that datum, at the triple of the spectral clauses.
* `FastDynamo.MainTheoremNormalized`: every clause of Theorem 1.2 for the normalised velocity
  of Remark 1.6, `mainTheoremNormalized_holds`.
* `FastDynamo.Finish.MagneticScaleMain`: `cor:magnetic-scale` at the witnesses of the theorem,
  `main_theorem_magnetic_scale`.
* `FastDynamo.Dynamics.Assembly.FastDynamo`: the definitions of dynamo, fast dynamo and slow
  dynamo of §1.1, and `isFastDynamo_mainVelocity`.
* `FastDynamo.Dynamics.Assembly.SemigroupSpectralGrowth`: Lemma A.1 as one statement,
  `semigroupSpectralGrowth_holds`.
* `FastDynamo.Dynamics.MainLagrangianClauses`: the dynamical half at the same
  velocity — `mainTheoremDynamical_holds` for the theorem's own two clauses
  (its last sentence) and `mainTheoremLagrangian_holds` for the larger bundle
  `prop:particle-flow` + `cor:ideal-growth` it is projected from — hence Theorem 1.2
  in full, `mainTheoremComplete_holds`; the ideal solution group as the unique solution group
  of the ideal induction equation, `existsUnique_isIdealSolutionGroup_mainLiteralVelocity`;
  and the ideal–resistive gap `ideal_resistive_gap_holds` (the chain
  `γ_id(u) = 0 < γ₀ ≤ liminf_{ε ↓ 0} γ(u, ε)`, which joins the last clause of the theorem to
  `eq:main-growth-conclusion`; the paper states it as no single result).
* `FastDynamo.Dynamics.VanishingDiffusivity.Limit`: Remark 1.7,
  `tendstoUniformlyOn_resistiveEvolution_mainIdealGroup`.

**Citations.**  Throughout this library the paper is cited by its LaTeX labels
(`thm:main`, `lem:axial-recovery`, `eq:main-thm-growth`, …), by the theorem numbers of the
paper (Theorem 1.2, Proposition 7.1, …) and by its section numbers (§1–§8, Appendix A).  The
Lean identifiers say `transverse` where the paper says "horizontal"; the correspondence is
recorded in `FastDynamo/Conventions.lean`.

The proof is assembled from the following layers (see `docs/MODULE_MAP.md`):

* `Conventions`, `Fourier/*`, `Analysis/*`: the torus, Fourier-graph Sobolev
  spaces, weak derivatives and Leibniz rules, periodic multipliers and cut-offs,
  whole-plane Fourier analysis, `H²` regularity, Rellich compactness, and the literal
  three-torus with its gradient, the mollifier `J_δ` and the Friedrichs commutator.
* `Operator/*`: domain operators, resolvents, Riesz projections, Fredholm and
  compactness theory, the resolvent set and spectrum of a partially defined operator,
  holomorphy of resolvents, the compact embedding `H² ↪ L²` of the product torus, the reduced,
  auxiliary and physical induction operators, the horizontal two-component operator of
  `lem:torus-sector-basic`, and the whole-plane local operator.
* `Local/*`: the two-component local seed (`prop:local-seed`): modified Bessel functions,
  the Ponomarenko dispersion function and its certified root on a segment, the piecewise
  Cartesian mode of `lem:jump-horizontal-mode` and its regularity, the horizontal form
  operator with its resolvent, its spectrum in the right half-plane (isolated eigenvalues)
  and local Riesz projection, the smoothed helical velocity, and the seed record
  `LocalSeedC2`.
* `Reduction/*`: the scaling identity `eq:scaling` of `lem:exact-renormalization`.
* `Global/*`: scale families, cell placement, the global velocity and its regularity
  (including its derivative at every point), the parameter choice, the background resolvent
  of `prop:background-resolvent` and its holomorphy, and the rescaled local resolvents of
  `cor:scaled-local-resolvents`, the torus charts and cut-offs, the two-summand parametrix and
  its error (`lem:parametrix-error`), the contour resolvent and the non-zero Riesz projection,
  the spectral transfer (`prop:global-spectral-transfer`), and the witnesses of the main
  theorem.
* `Finish/*`: the recovery of the axial component (`lem:axial-recovery`), divergence-free
  complex eigenmodes, the real datum and its exact `L²` norm law, the strong-solution
  certificate, the magnetic-length bounds and `cor:magnetic-scale`, the zero mean of the
  constructed fields (Remark 1.5, `rem:scope-intro`), Remark 1.4 on the real part of the
  mode, and the negative-diffusivity counterexample.
* `Dynamics/*` (Eulerian): the semigroup interface, uniqueness of forward strong
  solutions, the a priori energy bound and the energy identity `eq:energy-competition`, the
  Hille–Yosida generation theorem built from scratch in dissipative form, the product
  induction semigroup and its solenoidal restriction, and the growth rate `γ(u, ε)` with its
  floor and ceiling `γ₀ ≤ γ(u, ε) ≤ ‖∇⊥ u‖_∞` at the explicit witnesses; the growth bound of a
  semigroup as a limit (`Dynamics/GrowthBoundLimit.lean`) and its time rescaling; the
  generator of a semigroup, analytic semigroups, compactness and spectral mapping, the
  generator `L_{ε,u}` of the semigroup on `L²_σ`, and `γ(u, ε)` as a limit and as the
  spectral bound — Lemma A.1 (`lem:semigroup-spectral-growth`), stated as one structure in
  `Dynamics/Assembly/SemigroupSpectralGrowth.lean`; the dynamo definitions of §1.1.
* `Dynamics/Assembly/{NegativeSobolevResolvent,PhysicalInductionUniqueness,SemigroupOrbit}.lean`:
  "its solution" of `eq:main-thm-growth` — every forward strong solution of the curl-form
  equation with datum in `L²_σ` is the semigroup orbit, and the real datum's orbit is the
  explicit real curve and obeys the exact growth law, at the triple of the spectral clauses
  `MainPhysicalClausesAt` (`MainSemigroupOrbitClauses`).
* `Dynamics/ParticleFlow.lean`: the statement layer of the dynamical half —
  `IsParticleFlow`, `HasZeroTopologicalEntropy`, `IsIdealInductionGroup`,
  `MainLagrangianClauses` and `MainTheoremDynamicalClauses`.
* `Dynamics/IdealWeakForm.lean`, `Dynamics/IdealWeakFormRescaling.lean`: the weak form of the
  ideal induction equation — `IsIdealTestField`, `IsIdealWeakSolution`,
  `IsIdealSolutionGroup` — and its behaviour under time rescaling.
* `Dynamics/Flow/*` (Lagrangian): the particle flow in closed form.  The plane
  rotation and the radial shear bounds, the cell profiles and the single-cell flow
  map, the accumulating plane flow and its `ℤ²`-periodisation, the Lipschitz
  constants, the descent to `Torus 3` (`literalFlow`), the packing bound on `T³`
  and the Lipschitz-iterate entropy criterion, the derivative `DΦ_t` and its
  complexification, the variational equation `eq:flow-variational-equation`, measure
  preservation, the ODE itself (`isParticleFlow_literalFlow`) and its uniqueness by Grönwall
  on the lifts (`IsParticleFlow.unique`, `existsUnique_isParticleFlow_mainLiteralVelocity`);
  `eq:explicit-particle-flow` at torus level with the fixed points and the centre
  speed, and, in `Flow/LipschitzRate.lean`, the optimal Lipschitz constant `lipConst`
  with `lim_{|t| → ∞} |t|⁻¹ log Lip(Φ_t) = 0` (`prop:particle-flow`).
* `Dynamics/Ideal/*`: the ideal induction group.  Gradient orthogonality
  on the literal torus, the Cauchy transport operator `𝒯₀(t)` on `L²(T³;ℂ³)`,
  the truncated flows that make the solenoidal subspace invariant, strong
  continuity, the corestricted group `idealGroup` with
  `isIdealInductionGroup_idealGroup`; the velocity gradient and the stretching operator,
  the Cauchy orbits as weak solutions, the extension of the weak identity to Lipschitz test
  fields, and the uniqueness of weak solutions and of the solution group.
* `Dynamics/MainLagrangianClauses.lean`: the assembly — `MainLagrangianClauses` and
  `MainTheoremDynamicalClauses` at the constructed velocity, `MainTheoremLagrangian`,
  `MainTheoremDynamical`, `MainTheoremComplete`, the unique solution group and the
  ideal–resistive gap; `Dynamics/NormalizedLagrangianClauses.lean` the same for the
  normalised velocity.
* `Dynamics/VanishingDiffusivity/*`: Remark 1.7 — the bridge between the product picture of
  the resistive semigroup and the literal picture of the ideal group, the energy estimate
  against the mollified ideal orbit, and the limit `ε ↓ 0`.

* `Palomar/*`: Theorem 1.2 in the form of the Challenge statement (`Challenge.lean` at the
  root of the repository), which uses only mathlib notions and fourteen short definitions.
  `Palomar/Statement.lean` repeats those definitions character for character (namespace
  `FastDynamoChallenge`); the other modules identify them with the library's objects — Fourier
  coefficients, `L²_σ`, `H²`, the Fourier symbol of the induction operator, the induction
  semigroup, the particle flow, the ideal solution group — and `Palomar/Main.lean` proves the
  statement (`challenge_statement`).

`Check.lean` and `FastDynamo/AxiomAudit.lean` form the audited surface; the
release gate is `scripts/audit.sh`.
-/
