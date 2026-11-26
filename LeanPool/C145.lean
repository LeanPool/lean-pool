/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

module

public import LeanPool.C145.C145DRE8CommonUnit
public import LeanPool.C145.C145DRE8Frobenius
public import LeanPool.C145.C145DRE8HilbertStability
public import LeanPool.C145.C145DRE8ProjectionResiduals
public import LeanPool.C145.C145N6LiteralRows
public import LeanPool.C145.C145N6Squarefree
public import LeanPool.C145.C145PhysicalFrame
public import LeanPool.C145.C145ThreePlaneFactor
public import LeanPool.C145.C145WeightedGraph
public import LeanPool.C145.C145CyclicSpectral
public import LeanPool.C145.C145DRE8PhysicalTensor
public import LeanPool.C145.C145H2NumeratorData
public import LeanPool.C145.C145N6LineExclusion
public import LeanPool.C145.C145DRE8SliceRigidity
public import LeanPool.C145.C145DRE8TensorSpace
public import LeanPool.C145.C145H1ModalCalibration
public import LeanPool.C145.C145H2GridResidueInverse
public import LeanPool.C145.C145H2PositiveGrid
public import LeanPool.C145.C145CompleteOrdinaryH2Kernel
public import LeanPool.C145.C145SignedGroundPulseCalibration
public import LeanPool.C145.C145ReceivingLagrangeMoments
public import LeanPool.C145.C145SixFixedProducts
public import LeanPool.C145.C145DRE8WeightedKernel
public import LeanPool.C145.C145EightAffineFamilies
public import LeanPool.C145.C145DRE8CubicCancellation
public import LeanPool.C145.C145DRE8PositiveGridKernel
public import LeanPool.C145.C145PhysicalTraceResidue
public import LeanPool.C145.C145DRE8SpectralContraction
public import LeanPool.C145.C145N6TraceLine
public import LeanPool.C145.C145SmallPhysicalTraceSeparation
public import LeanPool.C145.C145CoordinatePermutation
public import LeanPool.C145.C145DRE8OptimalContraction
public import LeanPool.C145.C145DRE8OrthogonalTransport
public import LeanPool.C145.C145N6ResponseLine
public import LeanPool.C145.C145DRE8CalibratedUniqueness
public import LeanPool.C145.C145N6HelmertFrame
public import LeanPool.C145.C145OrientedEigenframe
public import LeanPool.C145.C145UncalibratedSmallH2
public import LeanPool.C145.C145DelayKernelTransfer
public import LeanPool.C145.C145N6PhysicalWitness
public import LeanPool.C145.C145ActualResponseC2
public import LeanPool.C145.C145N6CalibratedTransport
public import LeanPool.C145.C145TimeKernelContinuation
public import LeanPool.C145.C145ActualTimeConvolution
public import LeanPool.C145.C145N6PositiveGraph
public import LeanPool.C145.C145N6Uncalibrated
public import LeanPool.C145.C145ObservedKernelRecovery
public import LeanPool.C145.C145FixedHorizonSmallInverse
public import LeanPool.C145.C145N6TimeKernels
public import LeanPool.C145.C145GraphSpectralRealization
public import LeanPool.C145.C145N6OrdinaryJets
public import LeanPool.C145.C145DRE8ActualFrame
public import LeanPool.C145.C145N6GraphResponse
public import LeanPool.C145.C145PaperDomainChecks
public import LeanPool.C145.C145PaperRealizationInvariance
public import LeanPool.C145.C145DRE8ActualCalibratedInverse
public import LeanPool.C145.C145DRE8KrylovSlices
public import LeanPool.C145.C145DRE8PhysicalStability
public import LeanPool.C145.C145DRE8SignedGroundResidue
public import LeanPool.C145.C145N6OriginalGraph
public import LeanPool.C145.C145DRE8JointSignatureInverse
public import LeanPool.C145.C145DRE8TransferInverse
public import LeanPool.C145.C145PaperStability
public import LeanPool.C145.C145DRE8JointTransferInverse
public import LeanPool.C145.C145DRE8OriginalGraphInverse
public import LeanPool.C145.C145PaperResidualInvariance
public import LeanPool.C145.C145DRE8JointOriginalGraph
public import LeanPool.C145.C145PaperActualResponse
public import LeanPool.C145.C145PaperPositiveWitness
public import LeanPool.C145.C145PaperApplication
public import LeanPool.C145.C145PaperTheoremC

/-!
# Exact single-port graph identification from two response derivatives

Source: url:https://github.com/VanGogh7777/c145-lean/blob/75d25568c084c8aab4faee30bd94905a6d20c3ad/paper/C145_v0.6.pdf
Authors: Mark Gladden
Status: verified
Main declarations: `C145.PaperActualResponse.selected_response_theoremA_graph`,
  `C145N6Frame.literal_N6_original_graph_identification`
Tags: graph identification, inverse problems, reaction diffusion
MSC: 93B30, 05C50
-/
