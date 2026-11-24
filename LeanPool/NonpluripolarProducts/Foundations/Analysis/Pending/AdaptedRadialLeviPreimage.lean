/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AdaptedRadialKernel
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RadialLeviPreimage
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Radial Levi preimages in adapted complex coordinates

This file transfers the standard radial Poisson certificate through the
complex-linear coordinates used by the distribution regularization.  The
normalization of the coordinate kernel depends on the chosen Haar measure;
the positive Haar scalar is therefore kept explicitly rather than identifying
two differently normalized densities.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.AdaptedRadialLeviPreimage

open FirstPass
open FirstPass.MongeAmpere
open AdaptedRadialKernel
open HolomorphicPullback
open RadialLeviPreimage
open RadialPoissonCertificate
open RadialPoissonPrimitive

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

/-- Levi forms commute with pullback by a continuous complex-linear map. -/
theorem leviForm_comp_complexLinearMap
    (A : E →L[ℂ] F) {u : F → ℝ} (hu : ContDiff ℝ 2 u)
    (x v : E) :
    leviForm (fun y : E ↦ u (A y)) x v = leviForm u (A x) (A v) := by
  let AR : E →L[ℝ] F := A.restrictScalars ℝ
  rw [leviForm, leviForm,
    show realHessian (fun y : E ↦ u (A y)) x v v =
        realHessian u (A x) (A v) (A v) by
      simpa [AR] using realHessian_comp_affine hu AR 0 x v v,
    show realHessian (fun y : E ↦ u (A y)) x (Complex.I • v) (Complex.I • v) =
        realHessian u (A x) (Complex.I • A v) (Complex.I • A v) by
      simpa [AR] using
        realHessian_comp_affine hu AR 0 x
          (Complex.I • v) (Complex.I • v)]

section CoordinateNormalization

variable {n : ℕ} (ν : Measure (ComplexModel n)) [ν.IsAddHaarMeasure]

/-- The integral used to normalize a coordinate radial kernel differs from
the standard-volume integral by the positive Haar scalar. -/
theorem integral_explicitRadialRaw_eq_haarScalar_mul
    (R : ℝ) (hR : 0 < R) (j : ℕ) :
    (∫ x : ComplexModel n, explicitRadialRaw R hR j x ∂ν) =
      (Measure.addHaarScalarFactor ν volume : ℝ) *
        ∫ x : ComplexModel n, explicitRadialRaw R hR j x := by
  simpa only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] using
    (Measure.integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport ν volume
      (explicitRadialRaw_contDiff R hR j).continuous
      (explicitRadialRaw_hasCompactSupport R hR j))

/-- A coordinate-normalized kernel is the standard-volume kernel divided by
the Haar scalar. -/
theorem coordinateRadialKernel_eq_inv_haarScalar_mul
    (R : ℝ) (hR : 0 < R) (j : ℕ) (x : ComplexModel n) :
    coordinateRadialKernel ν R hR j x =
      (Measure.addHaarScalarFactor ν volume : ℝ)⁻¹ *
        explicitRadialKernel R hR j x := by
  simp only [explicitRadialKernel, coordinateRadialKernel,
    integral_explicitRadialRaw_eq_haarScalar_mul ν R hR j]
  have hc : (Measure.addHaarScalarFactor ν volume : ℝ) ≠ 0 := by
    exact_mod_cast
      (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume).ne'
  have hi : (∫ y : ComplexModel n, explicitRadialRaw R hR j y) ≠ 0 :=
    (explicitRadialRaw_integral_pos R hR j).ne'
  field_simp [hc, hi]

end CoordinateNormalization

section Adapted

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

local instance : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
  adaptedCoordinateMeasure_isAddHaarMeasure μ

/-- The adapted complex coordinate directions corresponding to the standard
coordinate frame. -/
noncomputable def adaptedCoordinateVector
    (j : Fin (Module.finrank ℂ E)) : E :=
  (adaptedComplexModelEquiv (E := E)).symm (coordinateVector j)

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem adaptedComplexModelEquiv_adaptedCoordinateVector
    (j : Fin (Module.finrank ℂ E)) :
    adaptedComplexModelEquiv (adaptedCoordinateVector (E := E) j) =
      coordinateVector j :=
  (adaptedComplexModelEquiv (E := E)).apply_symm_apply _

/-- The standard Poisson potential, divided by the Haar scalar and pulled
back through the adapted complex coordinates. -/
noncomputable def adaptedRadialPoissonPotential
    (R : ℝ) (hR : 0 < R) (a b : ℕ) (x : E) : ℝ :=
  (Measure.addHaarScalarFactor (adaptedCoordinateMeasure μ) volume : ℝ)⁻¹ *
    explicitRadialPoissonPotential R hR a b (adaptedComplexModelEquiv x)

/-- The adapted Poisson potential is radial in the transported complex
coordinates: it is a one-variable profile of the squared coordinate norm. -/
theorem adaptedRadialPoissonPotential_eq_profile
    (R : ℝ) (hR : 0 < R) (a b : ℕ) :
    ∃ G : ℝ → ℝ, ∀ x : E,
      adaptedRadialPoissonPotential μ R hR a b x =
        G (‖adaptedComplexModelEquiv x‖ ^ 2) := by
  refine ⟨fun s ↦
      (Measure.addHaarScalarFactor
        (adaptedCoordinateMeasure μ) volume : ℝ)⁻¹ *
        radialPoissonPrimitive (Module.finrank ℂ E)
          (explicitRadialKernelSqDifference
            (n := Module.finrank ℂ E) R hR a b)
          ((R / ((a : ℝ) + 1)) ^ 2) s, ?_⟩
  intro x
  rfl

/-- In particular, the adapted potential is invariant under complex scalar
rotations in its transported coordinates. -/
theorem adaptedRadialPoissonPotential_unitary
    (R : ℝ) (hR : 0 < R) (a b : ℕ)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : E) :
    adaptedRadialPoissonPotential μ R hR a b
        (adaptedComplexModelEquiv.symm
          (ζ • adaptedComplexModelEquiv x)) =
      adaptedRadialPoissonPotential μ R hR a b x := by
  simp [adaptedRadialPoissonPotential, explicitRadialPoissonPotential,
    norm_smul, hζ]

theorem adaptedRadialPoissonPotential_contDiff
    (hn : 0 < Module.finrank ℂ E)
    (R : ℝ) (hR : 0 < R) (a b : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (adaptedRadialPoissonPotential μ R hR a b) := by
  exact contDiff_const.mul
    ((explicitRadialPoissonPotential_contDiff hn R hR a b).comp
      ((adaptedComplexModelEquiv (E := E)).toContinuousLinearMap.restrictScalars ℝ).contDiff)

theorem adaptedRadialPoissonPotential_nonneg
    (hn : 0 < Module.finrank ℂ E)
    (R : ℝ) (hR : 0 < R) {a b : ℕ} (hab : a ≤ b) (x : E) :
    0 ≤ adaptedRadialPoissonPotential μ R hR a b x := by
  exact mul_nonneg
    (inv_nonneg.mpr (NNReal.coe_nonneg
      (Measure.addHaarScalarFactor (adaptedCoordinateMeasure μ) volume)))
    (explicitRadialPoissonPotential_nonneg hn R hR hab
      (adaptedComplexModelEquiv x))

/-- The adapted Poisson potential vanishes at and beyond the outer coordinate
radius of the first kernel scale. -/
theorem adaptedRadialPoissonPotential_eq_zero_of_outer
    (hn : 0 < Module.finrank ℂ E)
    (R : ℝ) (hR : 0 < R) {a b : ℕ} (hab : a ≤ b) {x : E}
    (hx : R / ((a : ℝ) + 1) ≤ ‖adaptedComplexModelEquiv x‖) :
    adaptedRadialPoissonPotential μ R hR a b x = 0 := by
  change
    (Measure.addHaarScalarFactor
      (adaptedCoordinateMeasure μ) volume : ℝ)⁻¹ *
        explicitRadialPoissonPotential R hR a b
          (adaptedComplexModelEquiv x) = 0
  rw [explicitRadialPoissonPotential_eq_zero_of_outer hn R hR hab hx,
    mul_zero]

theorem adaptedRadialPoissonPotential_hasCompactSupport
    (hn : 0 < Module.finrank ℂ E)
    (R : ℝ) (hR : 0 < R) {a b : ℕ} (hab : a ≤ b) :
    HasCompactSupport
      (adaptedRadialPoissonPotential μ R hR a b) := by
  exact ((explicitRadialPoissonPotential_hasCompactSupport
      hn R hR hab).comp_homeomorph
        (adaptedComplexModelEquiv (E := E)).toHomeomorph).mul_left

/-- The topological support of the adapted potential lies in the pullback of
the first kernel's outer coordinate ball. -/
theorem adaptedRadialPoissonPotential_tsupport_subset
    (hn : 0 < Module.finrank ℂ E)
    (R : ℝ) (hR : 0 < R) {a b : ℕ} (hab : a ≤ b) :
    tsupport (adaptedRadialPoissonPotential μ R hR a b) ⊆
      adaptedComplexModelEquiv ⁻¹'
        closedBall 0 (R / ((a : ℝ) + 1)) := by
  apply closure_minimal
  · intro x hx
    change adaptedComplexModelEquiv x ∈
      closedBall 0 (R / ((a : ℝ) + 1))
    simp only [mem_closedBall, dist_zero_right]
    by_contra hnorm
    have hrx : R / ((a : ℝ) + 1) ≤ ‖adaptedComplexModelEquiv x‖ :=
      le_of_not_ge hnorm
    exact hx (adaptedRadialPoissonPotential_eq_zero_of_outer
      μ hn R hR hab hrx)
  · exact isClosed_closedBall.preimage adaptedComplexModelEquiv.continuous

/-- Four times the sum of Levi forms in the adapted coordinate directions is
the difference of the two adapted normalized kernels. -/
theorem four_mul_sum_leviForm_adaptedRadialPoissonPotential_eq_kernel_sub
    (hn : 0 < Module.finrank ℂ E)
    (R : ℝ) (hR : 0 < R) (a b : ℕ) (x : E) :
    4 * ∑ j : Fin (Module.finrank ℂ E),
      leviForm (adaptedRadialPoissonPotential μ R hR a b) x
        (adaptedCoordinateVector (E := E) j) =
      adaptedRadialKernel μ R hR a x -
        adaptedRadialKernel μ R hR b x := by
  let u : ComplexModel (Module.finrank ℂ E) → ℝ :=
    explicitRadialPoissonPotential R hR a b
  have hu : ContDiff ℝ 2 u :=
    (explicitRadialPoissonPotential_contDiff hn R hR a b).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcomp : ∀ j : Fin (Module.finrank ℂ E),
      leviForm (adaptedRadialPoissonPotential μ R hR a b) x
          (adaptedCoordinateVector (E := E) j) =
        (Measure.addHaarScalarFactor
          (adaptedCoordinateMeasure μ) volume : ℝ)⁻¹ *
          leviForm u (adaptedComplexModelEquiv x) (coordinateVector j) := by
    intro j
    change leviForm
      ((Measure.addHaarScalarFactor
        (adaptedCoordinateMeasure μ) volume : ℝ)⁻¹ •
          fun y : E ↦ u (adaptedComplexModelEquiv y)) x
        (adaptedCoordinateVector (E := E) j) = _
    rw [leviForm_smul]
    · congr 1
      have hlev := leviForm_comp_complexLinearMap
        (adaptedComplexModelEquiv (E := E)).toContinuousLinearMap hu x
          (adaptedCoordinateVector (E := E) j)
      have hA :
          (adaptedComplexModelEquiv (E := E)).toContinuousLinearMap
              (adaptedCoordinateVector (E := E) j) =
            coordinateVector j :=
        (adaptedComplexModelEquiv (E := E)).apply_symm_apply _
      rw [hA] at hlev
      change leviForm
          (fun y : E ↦ u (adaptedComplexModelEquiv y)) x
            (adaptedCoordinateVector (E := E) j) =
        leviForm u (adaptedComplexModelEquiv x) (coordinateVector j) at hlev
      exact hlev
    · exact (hu.comp
        ((adaptedComplexModelEquiv (E := E)).toContinuousLinearMap.restrictScalars
          ℝ).contDiff).contDiffAt
  simp_rw [hcomp]
  rw [← Finset.mul_sum]
  change 4 *
      ((Measure.addHaarScalarFactor
        (adaptedCoordinateMeasure μ) volume : ℝ)⁻¹ *
        coordinateLeviTrace u (adaptedComplexModelEquiv x)) = _
  calc
    _ = (Measure.addHaarScalarFactor
          (adaptedCoordinateMeasure μ) volume : ℝ)⁻¹ *
        (4 * coordinateLeviTrace u (adaptedComplexModelEquiv x)) := by ring
    _ = (Measure.addHaarScalarFactor
          (adaptedCoordinateMeasure μ) volume : ℝ)⁻¹ *
        (explicitRadialKernel R hR a (adaptedComplexModelEquiv x) -
          explicitRadialKernel R hR b (adaptedComplexModelEquiv x)) := by
      rw [four_mul_coordinateLeviTrace_explicitRadialPoissonPotential_eq_kernel_sub
        hn R hR a b]
    _ = adaptedRadialKernel μ R hR a x -
        adaptedRadialKernel μ R hR b x := by
      simp only [adaptedRadialKernel,
        coordinateRadialKernel_eq_inv_haarScalar_mul]
      ring

/-- In complex dimension zero the adapted normalized kernel is independent of
the scale index. -/
theorem adaptedRadialKernel_eq_of_finrank_complex_eq_zero
    (hzero : Module.finrank ℂ E = 0)
    (R : ℝ) (hR : 0 < R) (a b : ℕ) (x : E) :
    adaptedRadialKernel μ R hR a x =
      adaptedRadialKernel μ R hR b x := by
  let _ : FiniteDimensional ℂ E := finiteDimensional_complex_of_real
  have hdim : Module.finrank ℝ
      (ComplexModel (Module.finrank ℂ E)) = 0 := by
    rw [hzero]
    exact Module.finrank_zero_of_subsingleton
  have hall : ∀ y : E, y = 0 :=
    finrank_zero_iff_forall_zero.mp hzero
  have harg :
      adaptedComplexModelEquiv.symm
          (((((b : ℝ) + 1) / ((a : ℝ) + 1)) : ℝ) •
            adaptedComplexModelEquiv x) = x := by
    exact (hall _).trans (hall x).symm
  symm
  rw [adaptedRadialKernel_scale μ R hR a b x,
    hdim, pow_zero, one_mul, harg]

/-- Complete positive-dimensional adapted radial scale-difference
certificate. -/
theorem exists_adaptedRadialScaleDifferenceLeviPreimage
    (hn : 0 < Module.finrank ℂ E)
    (R : ℝ) (hR : 0 < R) {a b : ℕ} (hab : a ≤ b) :
    ∃ ψ : E → ℝ,
      (∃ G : ℝ → ℝ, ∀ x : E,
        ψ x = G (‖adaptedComplexModelEquiv x‖ ^ 2)) ∧
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      (∀ x, 0 ≤ ψ x) ∧
      HasCompactSupport ψ ∧
      tsupport ψ ⊆ adaptedComplexModelEquiv ⁻¹'
        closedBall 0 (R / ((a : ℝ) + 1)) ∧
      ∀ x,
        4 * ∑ j : Fin (Module.finrank ℂ E),
          leviForm ψ x (adaptedCoordinateVector (E := E) j) =
            adaptedRadialKernel μ R hR a x -
              adaptedRadialKernel μ R hR b x := by
  refine ⟨adaptedRadialPoissonPotential μ R hR a b,
    adaptedRadialPoissonPotential_eq_profile μ R hR a b,
    adaptedRadialPoissonPotential_contDiff μ hn R hR a b,
    fun x ↦ adaptedRadialPoissonPotential_nonneg μ hn R hR hab x,
    adaptedRadialPoissonPotential_hasCompactSupport μ hn R hR hab,
    adaptedRadialPoissonPotential_tsupport_subset μ hn R hR hab,
    fun x ↦ ?_⟩
  exact four_mul_sum_leviForm_adaptedRadialPoissonPotential_eq_kernel_sub
    μ hn R hR a b x

end Adapted

end SGPT.Foundations.Analysis.Pending.AdaptedRadialLeviPreimage
