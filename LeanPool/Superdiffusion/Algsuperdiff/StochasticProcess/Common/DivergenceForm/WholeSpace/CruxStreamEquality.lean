/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamLower
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamUpper

/-!
# CruxStreamEquality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Killed-resolvent equality for the stream field

The coefficient-dependent lower input is the stream field's
`WholeSpaceC0BarrierData`; the upper input is its localized split-skew
fixed-collar penalization estimate.  Thus no global small-contrast datum is
present.  The operator identification is stated against the C₀ operator
carried by the barrier structure.
-/

namespace DivergenceFormProcess.Form

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field
open HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceBarrierData

variable {M : ABKModel d} {omega : FullSample d M.gamma}
  (P : WholeSpaceBarrierData (streamWholeSpaceAnalyticData M omega))

/-- **S-free stream crux equality.**  On an exhaustion cube, the resolvent of
the whole-space stream process killed on leaving the compactified part domain
equals the continuous representative of the part resolvent. -/
theorem killedResolvent_eq_partResolvent_stream
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : WholeSpaceAnalyticData.KernelResolventIdentifiesAnalyticMinimal
      (streamWholeSpaceAnalyticData M omega) R)
    (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        ((streamWholeSpaceC0BarrierData M omega).resolvent
          ).toContractiveResolvent.operator mu g)
    (v : ℕ) (hVcube : P.V = wholeSpaceCube d v)
    {x : Vec d} (hx : x ∈ P.V) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' P.V)
        (OnePoint.isOpen_image_coe.mpr P.hV.isOpen) (P.lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y => ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d)) =
      ENNReal.ofReal (P.utilde x) := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  have hTop : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        WholeSpaceAnalyticData.analyticMinimalC0ResolventOfVanishing
          (streamWholeSpaceAnalyticData M omega)
          (streamWholeSpaceC0BarrierData M omega).vanishing mu g := by
    intro mu g
    exact hT mu g
  exact le_antisymm
    (P.killedResolvent_le_partResolvent_stream R hreg hcons hid v hVcube hx)
    (P.killedResolvent_ge_partResolvent_wholeSpace_of_c0Barrier
      (streamWholeSpaceC0BarrierData M omega) R hreg hid hTop hx)

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form
