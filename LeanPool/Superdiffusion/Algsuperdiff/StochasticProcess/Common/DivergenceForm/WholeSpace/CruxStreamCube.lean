/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxGeneralDomainCube
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamGeneralDomain

/-!
# CruxStreamCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/- Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong -/

/-! # S-free translated-cube exit identities for the stream process -/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section
variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable {M : ABKModel d} {omega : FullSample d M.gamma}

/-- The killed stream resolvent of one on a translated triadic cube is its
continuous Dirichlet resolvent. -/
theorem killedResolvent_one_eq_cubeSetAtOneResolvent_stream
    (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : (streamWholeSpaceAnalyticData M omega
      ).KernelResolventIdentifiesAnalyticMinimal R)
    (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        ((streamWholeSpaceC0BarrierData M omega).resolvent
          ).toContractiveResolvent.operator mu g)
    (y : Vec d) (n : ℤ) {lam : ℝ} (hlam : 0 < lam)
    {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
        (OnePoint.isOpen_image_coe.mpr (isOpen_cubeSetAt y n)) lam
        (fun _ => 1) (x : OnePoint (Vec d)) =
      ENNReal.ofReal ((streamWholeSpaceAnalyticData M omega
        ).cubeSetAtOneResolvent y n ⟨lam, hlam⟩ x) := by
  let A := streamWholeSpaceAnalyticData M omega
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  set P : WholeSpaceBarrierData A := A.cubeSetAtOneBarrierData y n ⟨lam, hlam⟩
  have hcrux := P.killedResolvent_eq_partResolvent_stream_general
    R hreg hcons hid hT hx
  have hobs : ∀ z ∈ ((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n,
      (1 : ℝ≥0∞) = PositiveC0ContractiveResolvent.onePointLiveExtension
        (fun w => ENNReal.ofReal (P.f w)) z := by
    rintro _ ⟨w, hw, rfl⟩
    rw [PositiveC0ContractiveResolvent.onePointLiveExtension_coe]
    change (1 : ℝ≥0∞) = ENNReal.ofReal (cubeSetAtOneDatum y n w)
    rw [cubeSetAtOneDatum_of_mem hw, ENNReal.ofReal_one]
  exact (killedResolvent_congr_of_eqOn _ _ _ _ lam hobs
    (x : OnePoint (Vec d))).trans hcrux

/-- The expected exit time from a translated triadic cube is the zero-shift
limit of its Dirichlet resolvents of one. -/
theorem lintegral_exitTime_eq_cubeSetAtExitFunction_stream
    (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : (streamWholeSpaceAnalyticData M omega
      ).KernelResolventIdentifiesAnalyticMinimal R)
    (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        ((streamWholeSpaceC0BarrierData M omega).resolvent
          ).toContractiveResolvent.operator mu g)
    (y : Vec d) (n : ℤ) {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    ∫⁻ path, ContinuousPath.exitTime
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) path
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (x : OnePoint (Vec d))) =
      (streamWholeSpaceAnalyticData M omega
        ).cubeSetAtExitFunction y n (x : OnePoint (Vec d)) := by
  let A := streamWholeSpaceAnalyticData M omega
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  refine IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq
    R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
    (A.cubeSetAtExitResolvent y n) (A.cubeSetAtExitFunction y n)
    (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
    (OnePoint.isOpen_image_coe.mpr (isOpen_cubeSetAt y n)) (fun lam hlam z hz => ?_)
    (fun _ _ => rfl) (Set.mem_image_of_mem _ hx)
  obtain ⟨w, hw, rfl⟩ := hz
  rw [A.cubeSetAtExitResolvent_coe y n hlam w]
  exact killedResolvent_one_eq_cubeSetAtOneResolvent_stream R hreg hcons hid hT
    y n hlam hw

end WholeSpaceAnalyticData
end
end DivergenceFormProcess.Form
