/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AdaptedKernelCoordinates
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicPullback

/-!
# Radial kernels in adapted complex coordinates

The explicit inner-product radial profile is normalized against an arbitrary
additive Haar measure on the standard complex model.  Pulling this normalized
kernel back through `adaptedComplexModelEquiv` gives a smooth nonnegative
approximate-identity kernel on any compatible finite-dimensional complex normed
space.  Its support, dilation law, and unitary symmetry are expressed in the
adapted coordinates rather than in the original norm.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.AdaptedRadialKernel

open FirstPass
open HolomorphicPullback

variable {n : ℕ}

section Pullback

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The coordinate-normalized radial kernel pulled back to the original
complex normed space. -/
noncomputable def adaptedRadialKernel (μ : Measure E) (R : ℝ) (hR : 0 < R)
    (j : ℕ) (x : E) : ℝ :=
  coordinateRadialKernel (adaptedCoordinateMeasure μ) R hR j
    (adaptedComplexModelEquiv x)

variable (μ : Measure E) [μ.IsAddHaarMeasure]

theorem adaptedRadialKernel_contDiff (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (adaptedRadialKernel μ R hR j) := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  exact (coordinateRadialKernel_contDiff (adaptedCoordinateMeasure μ) R hR j).comp
    ((adaptedComplexModelEquiv (E := E)).toContinuousLinearMap.restrictScalars ℝ).contDiff

theorem adaptedRadialKernel_nonneg (R : ℝ) (hR : 0 < R) (j : ℕ) (x : E) :
    0 ≤ adaptedRadialKernel μ R hR j x := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  exact coordinateRadialKernel_nonneg (adaptedCoordinateMeasure μ) R hR j _

theorem adaptedRadialKernel_integral_one (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ∫ x : E, adaptedRadialKernel μ R hR j x ∂μ = 1 := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  simpa only [adaptedRadialKernel] using
    (integral_comp_adaptedComplexModelEquiv μ
      (coordinateRadialKernel (adaptedCoordinateMeasure μ) R hR j))
      |>.trans (coordinateRadialKernel_integral_one
        (adaptedCoordinateMeasure μ) R hR j)

theorem adaptedRadialKernel_hasCompactSupport
    (R : ℝ) (hR : 0 < R) (j : ℕ) :
    HasCompactSupport (adaptedRadialKernel μ R hR j) := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  change HasCompactSupport (fun x : E ↦ coordinateRadialKernel
    (adaptedCoordinateMeasure μ) R hR j (adaptedComplexModelEquiv x))
  exact (coordinateRadialKernel_hasCompactSupport
    (adaptedCoordinateMeasure μ) R hR j).comp_homeomorph
      (adaptedComplexModelEquiv (E := E)).toHomeomorph

theorem adaptedRadialKernel_integrable (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Integrable (adaptedRadialKernel μ R hR j) μ := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  change Integrable (fun x : E ↦ coordinateRadialKernel
    (adaptedCoordinateMeasure μ) R hR j (adaptedComplexModelEquiv x)) μ
  exact (adaptedComplexModelEquiv_measurePreserving μ).integrable_comp_of_integrable
    (coordinateRadialKernel_integrable
      (adaptedCoordinateMeasure μ) R hR j)

/-- The pulled-back kernel is supported in the inverse image of its coordinate
closed ball. -/
theorem adaptedRadialKernel_tsupport_subset (R : ℝ) (hR : 0 < R) (j : ℕ) :
    tsupport (adaptedRadialKernel μ R hR j) ⊆
      adaptedComplexModelEquiv ⁻¹'
        closedBall 0 (R / ((j : ℝ) + 1)) := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  apply closure_minimal
  · intro x hx
    have hx' : adaptedComplexModelEquiv x ∈
        Function.support
          (coordinateRadialKernel (adaptedCoordinateMeasure μ) R hR j) := hx
    rw [coordinateRadialKernel_support (adaptedCoordinateMeasure μ) R hR j] at hx'
    change adaptedComplexModelEquiv x ∈
      closedBall 0 (R / ((j : ℝ) + 1))
    rw [← closure_ball _ (by positivity : R / ((j : ℝ) + 1) ≠ 0)]
    exact subset_closure hx'
  · exact isClosed_closedBall.preimage adaptedComplexModelEquiv.continuous

/-- Norm form of `adaptedRadialKernel_tsupport_subset`. -/
theorem adaptedRadialKernel_tsupport_subset_norm (R : ℝ) (hR : 0 < R) (j : ℕ) :
    tsupport (adaptedRadialKernel μ R hR j) ⊆
      {x | ‖adaptedComplexModelEquiv x‖ ≤ R / ((j : ℝ) + 1)} := by
  intro x hx
  exact mem_closedBall_zero_iff.mp
    (adaptedRadialKernel_tsupport_subset μ R hR j hx)

theorem adaptedRadialKernel_unitary (R : ℝ) (hR : 0 < R) (j : ℕ)
    (a : ℂ) (ha : ‖a‖ = 1) (x : E) :
    adaptedRadialKernel μ R hR j
        (adaptedComplexModelEquiv.symm (a • adaptedComplexModelEquiv x)) =
      adaptedRadialKernel μ R hR j x := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  simp only [adaptedRadialKernel, ContinuousLinearEquiv.apply_symm_apply]
  exact coordinateRadialKernel_unitary
    (adaptedCoordinateMeasure μ) R hR j a ha _

theorem adaptedRadialKernel_scale (R : ℝ) (hR : 0 < R) (a b : ℕ) (x : E) :
    adaptedRadialKernel μ R hR b x =
      (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^
          Module.finrank ℝ
            (ComplexModel (Module.finrank ℂ E)) *
        adaptedRadialKernel μ R hR a
          (adaptedComplexModelEquiv.symm
            (((((b : ℝ) + 1) / ((a : ℝ) + 1)) : ℝ) •
              adaptedComplexModelEquiv x)) := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  simp only [adaptedRadialKernel, ContinuousLinearEquiv.apply_symm_apply]
  exact coordinateRadialKernel_scale
    (adaptedCoordinateMeasure μ) R hR a b _

end Pullback

end SGPT.Foundations.Analysis.Pending.AdaptedRadialKernel
