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

/-- The explicit radial profile normalized against an arbitrary additive Haar
measure on the standard complex model. -/
noncomputable def coordinateRadialKernel
    (ν : Measure (ComplexModel n)) (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : ℝ :=
  explicitRadialRaw R hR j x /
    ∫ y : ComplexModel n, explicitRadialRaw R hR j y ∂ν

variable (ν : Measure (ComplexModel n)) [ν.IsAddHaarMeasure]

theorem explicitRadialRaw_integrable (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Integrable (explicitRadialRaw (n := n) R hR j) ν :=
  (explicitRadialRaw_contDiff R hR j).continuous.integrable_of_hasCompactSupport
    (explicitRadialRaw_hasCompactSupport R hR j)

theorem explicitRadialRaw_integral_pos (R : ℝ) (hR : 0 < R) (j : ℕ) :
    0 < ∫ x : ComplexModel n, explicitRadialRaw R hR j x ∂ν := by
  refine (integral_pos_iff_support_of_nonneg
    (explicitRadialRaw_nonneg R hR j)
    (explicitRadialRaw_integrable ν R hR j)).mpr ?_
  rw [explicitRadialRaw_support R hR j]
  exact measure_ball_pos ν 0 (by positivity)

omit [ν.IsAddHaarMeasure] in
theorem coordinateRadialKernel_contDiff (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateRadialKernel ν R hR j) :=
  (explicitRadialRaw_contDiff R hR j).div_const _

theorem coordinateRadialKernel_nonneg (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : 0 ≤ coordinateRadialKernel ν R hR j x :=
  div_nonneg (explicitRadialRaw_nonneg R hR j x)
    (explicitRadialRaw_integral_pos ν R hR j).le

theorem coordinateRadialKernel_integral_one (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ∫ x : ComplexModel n, coordinateRadialKernel ν R hR j x ∂ν = 1 := by
  simp_rw [coordinateRadialKernel, div_eq_mul_inv,
    mul_comm (explicitRadialRaw R hR j _), ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel₀ (explicitRadialRaw_integral_pos ν R hR j).ne'

theorem coordinateRadialKernel_support (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Function.support (coordinateRadialKernel ν R hR j) =
      ball 0 (R / ((j : ℝ) + 1)) := by
  have hpos := explicitRadialRaw_integral_pos (n := n) ν R hR j
  change Function.support (fun x : ComplexModel n ↦
    explicitRadialRaw R hR j x /
      ∫ y : ComplexModel n, explicitRadialRaw R hR j y ∂ν) = _
  rw [Function.support_div, Function.support_const hpos.ne', inter_univ,
    explicitRadialRaw_support R hR j]

theorem coordinateRadialKernel_tsupport (R : ℝ) (hR : 0 < R) (j : ℕ) :
    tsupport (coordinateRadialKernel ν R hR j) =
      closedBall 0 (R / ((j : ℝ) + 1)) := by
  rw [tsupport, coordinateRadialKernel_support ν R hR j,
    closure_ball _ (by positivity : R / ((j : ℝ) + 1) ≠ 0)]

theorem coordinateRadialKernel_hasCompactSupport
    (R : ℝ) (hR : 0 < R) (j : ℕ) :
    HasCompactSupport (coordinateRadialKernel ν R hR j) := by
  rw [HasCompactSupport, coordinateRadialKernel_tsupport ν R hR j]
  exact isCompact_closedBall _ _

theorem coordinateRadialKernel_integrable (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Integrable (coordinateRadialKernel ν R hR j) ν :=
  (coordinateRadialKernel_contDiff ν R hR j).continuous.integrable_of_hasCompactSupport
    (coordinateRadialKernel_hasCompactSupport ν R hR j)

theorem explicitRadialRaw_unitary (R : ℝ) (hR : 0 < R) (j : ℕ)
    (a : ℂ) (ha : ‖a‖ = 1) (x : ComplexModel n) :
    explicitRadialRaw R hR j (a • x) = explicitRadialRaw R hR j x := by
  simp [explicitRadialRaw, ContDiffBumpBase.ofInnerProductSpace, norm_smul, ha]

omit [ν.IsAddHaarMeasure] in
theorem coordinateRadialKernel_unitary (R : ℝ) (hR : 0 < R) (j : ℕ)
    (a : ℂ) (ha : ‖a‖ = 1) (x : ComplexModel n) :
    coordinateRadialKernel ν R hR j (a • x) =
      coordinateRadialKernel ν R hR j x := by
  rw [coordinateRadialKernel, coordinateRadialKernel,
    explicitRadialRaw_unitary R hR j a ha x]

theorem coordinateRadialKernel_scale (R : ℝ) (hR : 0 < R) (a b : ℕ)
    (x : ComplexModel n) :
    coordinateRadialKernel ν R hR b x =
      (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^
          Module.finrank ℝ (ComplexModel n) *
        coordinateRadialKernel ν R hR a
          ((((b : ℝ) + 1) / ((a : ℝ) + 1)) • x) := by
  let q : ℝ := ((b : ℝ) + 1) / ((a : ℝ) + 1)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hqpow : q ^ Module.finrank ℝ (ComplexModel n) ≠ 0 :=
    pow_ne_zero _ hq.ne'
  have hint :
      (∫ y : ComplexModel n, explicitRadialRaw R hR b y ∂ν) =
        (q ^ Module.finrank ℝ (ComplexModel n))⁻¹ *
          ∫ y : ComplexModel n, explicitRadialRaw R hR a y ∂ν := by
    rw [show (fun y : ComplexModel n ↦ explicitRadialRaw R hR b y) =
        fun y ↦ explicitRadialRaw R hR a (q • y) by
      funext y
      exact explicitRadialRaw_scale R hR a b y]
    simpa only [smul_eq_mul] using
      (Measure.integral_comp_smul_of_nonneg ν
        (explicitRadialRaw (n := n) R hR a) q (hR := hq.le))
  rw [coordinateRadialKernel, coordinateRadialKernel,
    explicitRadialRaw_scale R hR a b, hint]
  dsimp [q]
  field_simp [hqpow, (explicitRadialRaw_integral_pos (n := n) ν R hR a).ne']

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
