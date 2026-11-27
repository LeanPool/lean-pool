/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscAngularRecursion
public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscExponentialCoefficients

/-!
# Genuine compact-test Fubini for actual polydisc coefficients

The joint contour/test integral is absolutely integrable: continuity on
the compact coordinate ball times the actual test support supplies a
uniform kernel bound, and the angular inverse monomial has constant
norm. No coefficient/interchange identity is supplied as a premise.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Metric Set
open scoped BigOperators

private theorem compact_polydisc_kernel_bound (n : ℕ) (R : ℝ)
    (K : (Fin n → ℂ) → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hK : Continuous (fun y : (Fin n → ℂ) × EuclideanSpace ℝ (Fin 3) => K y.1 y.2))
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) (hfc : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closedBall (0 : Fin n → ℂ) R,
      ∀ x ∈ tsupport f, ‖K z x‖ ≤ M := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : Fin n → ℂ) R).prod hfc).exists_bound_of_continuousOn
    hK.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz x hx
  have hraw : ‖K z x‖ ≤ C := hC (z, x) ⟨hz, hx⟩
  exact hraw.trans (le_max_left C 0)

private theorem norm_polydisc_inverse_monomial (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (k : Fin n → ℕ) (θ : Fin n → ℝ) :
    ‖∏ j, (polydiscBoundaryPoint n R θ j)⁻¹ ^ k j‖ = ∏ j, R⁻¹ ^ k j := by
  simp only [norm_prod, norm_pow, norm_inv, norm_polydiscBoundaryPoint n hR]

private theorem norm_scalar_coefficient_product_le {a b w : ℂ} {M W : ℝ}
    (ha : ‖a‖ ≤ M) (hw : ‖w‖ = W) (hW : 0 ≤ W) :
    ‖a * b * w‖ ≤ (M * W) * ‖b‖ := by
  rw [norm_mul, norm_mul, hw]
  calc
    ‖a‖ * ‖b‖ * W ≤ M * ‖b‖ * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ha (norm_nonneg b)) hW
    _ = (M * W) * ‖b‖ := by ring

private theorem compact_polydisc_coefficient_pointwise_bound (n : ℕ) {R : ℝ} (hR : 0 < R)
    (K : (Fin n → ℂ) → EuclideanSpace ℝ (Fin 3) → ℂ)
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) (M : ℝ)
    (hK : ∀ z ∈ closedBall (0 : Fin n → ℂ) R, ∀ x ∈ tsupport f, ‖K z x‖ ≤ M)
    (k : Fin n → ℕ) (y : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 3)) :
    ‖K (polydiscBoundaryPoint n R y.1) y.2 * f y.2 *
      ∏ j, (polydiscBoundaryPoint n R y.1 j)⁻¹ ^ k j‖ ≤
        (M * ∏ j, R⁻¹ ^ k j) * ‖f y.2‖ := by
  by_cases hx : y.2 ∈ tsupport f
  · have hz : polydiscBoundaryPoint n R y.1 ∈ closedBall (0 : Fin n → ℂ) R := by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR.le]
      exact fun j => (norm_polydiscBoundaryPoint n hR.le y.1 j).le
    exact norm_scalar_coefficient_product_le
      (hK (polydiscBoundaryPoint n R y.1) hz y.2 hx)
      (norm_polydisc_inverse_monomial n hR.le k y.1)
      (Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr hR.le) (k j))
  · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, zero_mul, norm_zero, le_refl]

theorem integrable_compact_polydisc_coefficient_kernel (n : ℕ) {R : ℝ} (hR : 0 < R)
    (K : (Fin n → ℂ) → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hK : Continuous (fun y : (Fin n → ℂ) × EuclideanSpace ℝ (Fin 3) => K y.1 y.2))
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (k : Fin n → ℕ) :
    Integrable (fun y : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 3) =>
      K (polydiscBoundaryPoint n R y.1) y.2 * f y.2 *
        ∏ j, (polydiscBoundaryPoint n R y.1 j)⁻¹ ^ k j)
      ((polydiscAngleMeasure n).prod volume) := by
  obtain ⟨M, hM, hbound⟩ := compact_polydisc_kernel_bound n R K hK f hfc
  have hw : Continuous (fun θ : Fin n → ℝ =>
      ∏ j, (polydiscBoundaryPoint n R θ j)⁻¹ ^ k j) := by
    simpa only [one_mul] using continuous_boundary_coefficient_weight n hR
      (fun _ => (1 : ℂ)) continuous_const k
  have hg : Continuous (fun y : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 3) =>
      K (polydiscBoundaryPoint n R y.1) y.2 * f y.2 *
        ∏ j, (polydiscBoundaryPoint n R y.1 j)⁻¹ ^ k j) :=
    ((hK.comp (((continuous_polydiscBoundaryPoint n R).comp continuous_fst).prodMk
      continuous_snd)).mul (hf.comp continuous_snd)).mul (hw.comp continuous_fst)
  have hi : Integrable
      (fun y : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 3) =>
        (M * ∏ j, R⁻¹ ^ k j) * ‖f y.2‖) ((polydiscAngleMeasure n).prod volume) :=
    (integrable_const (M * ∏ j, R⁻¹ ^ k j) (μ := polydiscAngleMeasure n)).mul_prod
      (hf.integrable_of_hasCompactSupport (μ := volume) hfc).norm
  apply hi.mono' hg.aestronglyMeasurable
  exact Filter.Eventually.of_forall
    (compact_polydisc_coefficient_pointwise_bound n hR K f M hbound k)

theorem angularPolydiscCoefficient_compact_integral (n : ℕ) {R : ℝ} (hR : 0 < R)
    (K : (Fin n → ℂ) → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hK : Continuous (fun y : (Fin n → ℂ) × EuclideanSpace ℝ (Fin 3) => K y.1 y.2))
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (k : Fin n → ℕ) :
    angularPolydiscCoefficient n R (fun z => ∫ x, K z x * f x) k =
      ∫ x, angularPolydiscCoefficient n R (fun z => K z x) k * f x := by
  have hi := integrable_compact_polydisc_coefficient_kernel n hR K hK f hf hfc k
  let w := fun θ : Fin n → ℝ => ∏ j, (polydiscBoundaryPoint n R θ j)⁻¹ ^ k j
  change ((2 * Real.pi : ℂ) ^ n)⁻¹ *
    (∫ θ, (∫ x, K (polydiscBoundaryPoint n R θ) x * f x) * w θ ∂polydiscAngleMeasure n) = _
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap hi]
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  change ((2 * Real.pi : ℂ) ^ n)⁻¹ *
    (∫ θ, K (polydiscBoundaryPoint n R θ) x * f x * w θ ∂polydiscAngleMeasure n) = _
  have he (θ : Fin n → ℝ) :
      K (polydiscBoundaryPoint n R θ) x * f x * w θ =
        (K (polydiscBoundaryPoint n R θ) x * w θ) * f x := by ring
  simp_rw [he]
  rw [integral_mul_const]
  simp only [angularPolydiscCoefficient, polydiscAngularIntegral, w]
  ring

theorem polydiscCoefficient_eq_angular_of_continuous (n : ℕ) {R : ℝ} (hR : 0 < R)
    (F : (Fin n → ℂ) → ℂ) (hF : Continuous F) (k : Fin n → ℕ) :
    polydiscCoefficient n R F k = angularPolydiscCoefficient n R F k := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Fin n → ℂ) R).exists_bound_of_continuousOn
    hF.continuousOn
  apply (angularPolydiscCoefficient_eq n hR (M := max M 0) F
    (hF.comp (continuous_polydiscBoundaryPoint n R)) ?_ k).symm
  intro z hz
  have hzball : z ∈ closedBall (0 : Fin n → ℂ) R := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR.le]
    exact fun j => (hz j).le
  exact (hM z hzball).trans (le_max_left _ _)

theorem polydiscCoefficient_compact_integral (n : ℕ) {R : ℝ} (hR : 0 < R)
    (K : (Fin n → ℂ) → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hK : Continuous (fun y : (Fin n → ℂ) × EuclideanSpace ℝ (Fin 3) => K y.1 y.2))
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hF : Continuous (fun z => ∫ x, K z x * f x)) (k : Fin n → ℕ) :
    polydiscCoefficient n R (fun z => ∫ x, K z x * f x) k =
      ∫ x, polydiscCoefficient n R (fun z => K z x) k * f x := by
  rw [polydiscCoefficient_eq_angular_of_continuous n hR _ hF,
    angularPolydiscCoefficient_compact_integral n hR K hK f hf hfc]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  change angularPolydiscCoefficient n R (fun z => K z x) k * f x =
    polydiscCoefficient n R (fun z => K z x) k * f x
  have hKx : Continuous (fun z => K z x) :=
    hK.comp (continuous_id.prodMk continuous_const)
  rw [polydiscCoefficient_eq_angular_of_continuous n hR (fun z => K z x) hKx k]

end VacuumBellSeparation.Gaussian
