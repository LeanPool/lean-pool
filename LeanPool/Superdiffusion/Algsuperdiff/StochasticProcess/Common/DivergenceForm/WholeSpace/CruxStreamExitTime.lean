/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxGeneralDomainCube
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamEquality
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDEIdentificationLimit

/-!
# CruxStreamExitTime

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Exit times for the stream-field process

These are the exhaustion-cube exit-time consequences of the coefficient-generic
C₀ barrier comparison.  Their assumptions contain no global small-contrast
datum.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable {M : ABKModel d} {omega : FullSample d M.gamma}

/-- The killed stream resolvent of one on a centered exhaustion cube is its
Dirichlet resolvent. -/
theorem killedResolvent_one_eq_cubeExitResolvent_stream
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : (streamWholeSpaceAnalyticData M omega
      ).KernelResolventIdentifiesAnalyticMinimal R)
    (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        ((streamWholeSpaceC0BarrierData M omega).resolvent
          ).toContractiveResolvent.operator mu g)
    (v : ℕ) {lam : ℝ} (hlam : 0 < lam) {z : OnePoint (Vec d)}
    (hz : z ∈ ((↑) : Vec d → OnePoint (Vec d)) '' wholeSpaceCube d v) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' wholeSpaceCube d v)
        (OnePoint.isOpen_image_coe.mpr
          (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen) lam
        (fun _ => 1) z =
      (streamWholeSpaceAnalyticData M omega).cubeExitResolvent v lam z := by
  let A := streamWholeSpaceAnalyticData M omega
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  obtain ⟨x, hx, rfl⟩ := hz
  set P : WholeSpaceBarrierData A := A.cubeOneBarrierData v ⟨lam, hlam⟩ with hPdef
  have hcrux : IsConservative.killedResolvent R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' wholeSpaceCube d v)
      (OnePoint.isOpen_image_coe.mpr
        (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen) lam
      (PositiveC0ContractiveResolvent.onePointLiveExtension
        (fun y => ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d)) =
      ENNReal.ofReal (P.utilde x) :=
    P.killedResolvent_eq_partResolvent_stream R hreg hcons hid hT v rfl hx
  have hobs : ∀ y ∈ ((↑) : Vec d → OnePoint (Vec d)) '' wholeSpaceCube d v,
      (1 : ℝ≥0∞) = PositiveC0ContractiveResolvent.onePointLiveExtension
        (fun y => ENNReal.ofReal (P.f y)) y := by
    rintro _ ⟨y, hy, rfl⟩
    rw [PositiveC0ContractiveResolvent.onePointLiveExtension_coe]
    show (1 : ℝ≥0∞) = ENNReal.ofReal (cubeOneDatum d v y)
    rw [cubeOneDatum_of_mem hy, ENNReal.ofReal_one]
  refine ((killedResolvent_congr_of_eqOn _ _ _ _ lam hobs
      (x : OnePoint (Vec d))).trans hcrux).trans ?_
  exact (congrArg ENNReal.ofReal
    (eq_analyticCubeResolvent_of_isRepresentative A P.hV P.lam P.hf P.hfD
      P.hutildeCont P.hutildeRep v rfl hx)).trans
      (A.cubeExitResolvent_coe v hlam x).symm

/-- The expected exit time from a centered exhaustion cube is its analytic
zero-shift Dirichlet limit. -/
theorem lintegral_exitTime_eq_cubeExitFunction_stream
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : (streamWholeSpaceAnalyticData M omega
      ).KernelResolventIdentifiesAnalyticMinimal R)
    (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        ((streamWholeSpaceC0BarrierData M omega).resolvent
          ).toContractiveResolvent.operator mu g)
    (v : ℕ) {x : Vec d} (hx : x ∈ wholeSpaceCube d v) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    ∫⁻ path, ContinuousPath.exitTime
        (((↑) : Vec d → OnePoint (Vec d)) '' wholeSpaceCube d v) path
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (x : OnePoint (Vec d))) =
      (streamWholeSpaceAnalyticData M omega
        ).cubeExitFunction v (x : OnePoint (Vec d)) := by
  let A := streamWholeSpaceAnalyticData M omega
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  exact IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq
    R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
    (A.cubeExitResolvent v) (A.cubeExitFunction v)
    (((↑) : Vec d → OnePoint (Vec d)) '' wholeSpaceCube d v)
    (OnePoint.isOpen_image_coe.mpr
      (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen)
    (fun lam hlam z hz => killedResolvent_one_eq_cubeExitResolvent_stream
      R hreg hcons hid hT v hlam hz) (fun _ _ => rfl) (Set.mem_image_of_mem _ hx)

/-- The expected exit time from a centered exhaustion cube is finite for the
stream-field process. -/
theorem lintegral_exitTime_lt_top_stream
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : (streamWholeSpaceAnalyticData M omega
      ).KernelResolventIdentifiesAnalyticMinimal R)
    (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        ((streamWholeSpaceC0BarrierData M omega).resolvent
          ).toContractiveResolvent.operator mu g)
    (v : ℕ) {x : Vec d} (hx : x ∈ wholeSpaceCube d v) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    ∫⁻ path, ContinuousPath.exitTime
        (((↑) : Vec d → OnePoint (Vec d)) '' wholeSpaceCube d v) path
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (x : OnePoint (Vec d))) < ⊤ := by
  let A := streamWholeSpaceAnalyticData M omega
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  rw [lintegral_exitTime_eq_cubeExitFunction_stream R hreg hcons hid hT v hx,
    A.cubeExitFunction_coe_eq v x]
  exact ENNReal.ofReal_lt_top

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
