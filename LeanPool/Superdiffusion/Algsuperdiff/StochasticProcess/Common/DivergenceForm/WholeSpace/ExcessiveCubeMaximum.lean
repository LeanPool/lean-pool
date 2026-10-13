/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExcessiveCubeRemainder

/-!
# ExcessiveCubeMaximum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The pointwise maximum principle for the cube remainder

The cube remainder is a nonnegative weak supersolution of the shifted equation
with zero right-hand side, so the almost-everywhere maximum principle of the
part-domain layer applies to it.  Both sides of that inequality are continuous
on the cube, so it holds at every point of the cube; off the cube both sides
vanish, so it holds everywhere.

This is the `lam`-excessiveness inequality of the truncated barrier, in the
exact shape consumed by the exponential comparison of the process layer.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Topology
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d}

namespace WholeSpaceBarrierData

variable (P : WholeSpaceBarrierData A)

theorem boundedMeasurableToScalarL2_cubeBarrier (m : ℕ)
    (hVU : P.V ⊆ wholeSpaceCube d m) :
    boundedMeasurableToScalarL2 (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        ((P.measurable_cubeBarrier m).comp measurable_subtype_coe)
        (fun y => P.abs_cubeBarrier_le m y) =
      ZeroTraceSobolev.toL2 (P.cubeRemainder m hVU) := by
  refine (Lp.ext_iff).2 ?_
  filter_upwards [boundedMeasurableToScalarL2_coeFn
      (isOpenBoundedConvexDomain_wholeSpaceCube d m)
      ((P.measurable_cubeBarrier m).comp measurable_subtype_coe)
      (fun y => P.abs_cubeBarrier_le m y),
    P.cubeBarrier_ae m hVU,
    self_mem_ae_restrict
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen.measurableSet]
    with x h1 h2 hx
  rw [h1, domainExtension_of_mem hx]
  exact h2

/-- **The pointwise weak maximum principle on one exhaustion cube.** -/
theorem mul_analyticCubeResolvent_cubeBarrier_le (m : ℕ)
    (hVU : P.V ⊆ wholeSpaceCube d m) (mu : PositiveShift)
    (hmu : (P.lam : ℝ) < (mu : ℝ)) (x : Vec d) :
    (mu : ℝ) * A.analyticCubeResolvent mu (P.cubeBarrier m)
        (P.measurable_cubeBarrier m) (fun y => P.abs_cubeBarrier_le m y) m x ≤
      (mu : ℝ) / ((mu : ℝ) - (P.lam : ℝ)) * P.cubeBarrier m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · have hae := partDomainRemainder_resolvent_le_ae A.a P.hV
      (isOpenBoundedConvexDomain_wholeSpaceCube d m) hVU P.lam.property hmu
      A.hnu (A.cubeEllipticity m)
      (boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (P.hf.comp measurable_subtype_coe) (fun y => P.hfD y))
      (ae_nonneg_boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m) P.hf P.hf0 P.hfD)
    rw [P.partSolution_eq_of_cube m hVU] at hae
    have hcont : ContinuousOn (fun y => (mu : ℝ) *
        A.analyticCubeResolvent mu (P.cubeBarrier m)
          (P.measurable_cubeBarrier m) (fun z => P.abs_cubeBarrier_le m z) m y)
        (wholeSpaceCube d m) :=
      continuousOn_const.mul (A.continuousOn_analyticCubeResolvent mu
        (P.measurable_cubeBarrier m) (fun z => P.abs_cubeBarrier_le m z) m)
    have hcont2 : ContinuousOn (fun y =>
        (mu : ℝ) / ((mu : ℝ) - (P.lam : ℝ)) * P.cubeBarrier m y)
        (wholeSpaceCube d m) :=
      continuousOn_const.mul (P.continuousOn_cubeBarrier m)
    refine le_of_ae_le_of_continuousOn
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen hcont hcont2 ?_ x hx
    filter_upwards [A.analyticCubeResolvent_ae mu (P.measurable_cubeBarrier m)
        (fun z => P.abs_cubeBarrier_le m z) m, hae, P.cubeBarrier_ae m hVU]
      with y h1 h2 h3
    rw [h1, P.boundedMeasurableToScalarL2_cubeBarrier m hVU, h3]
    exact h2
  · have hzero := P.cubeBarrier_of_notMem m hVU hx
    rw [WholeSpaceAnalyticData.analyticCubeResolvent, dite_eq_right hx, hzero,
      mul_zero, mul_zero]

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form
