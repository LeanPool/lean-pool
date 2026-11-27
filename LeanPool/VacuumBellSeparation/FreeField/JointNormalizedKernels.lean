/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialKernelCoefficients
public import LeanPool.VacuumBellSeparation.Polynomial.SelectorTaylorBounds

/-!
# Literal normalized cross kernels for the joint-region construction

The normalized variables are u=x/s and w=y/s-e₀. Scaling them by s
feeds the already established physical covariance kernels. The fixed
Cauchy radius is 1/100; mass and separation remain in the original kernels.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian

/-- Normalized cross kernel in the two triples (u,w). -/
def jointNormalizedFieldKernel (μ s : ℝ) (z : Fin 6 → ℂ) : ℂ :=
  spatialSixFieldKernel μ s (fun j => (s : ℂ) * z j)

/-- Joint normalized momentum kernel given by `spatialSixMomentumKernel μ s (fun j => (s : ℂ) * z
j)`. -/
def jointNormalizedMomentumKernel (μ s : ℝ) (z : Fin 6 → ℂ) : ℂ :=
  spatialSixMomentumKernel μ s (fun j => (s : ℂ) * z j)

/-- Joint field envelope given by `(6 / s ^ 2) * Real.sqrt (1 + μ * s) * Real.exp (-μ * s / 2)`. -/
def jointFieldEnvelope (μ s : ℝ) : ℝ :=
  (6 / s ^ 2) * Real.sqrt (1 + μ * s) * Real.exp (-μ * s / 2)

/-- Joint momentum envelope given by `(128 / s ^ 4) * (1 + μ * s) * Real.sqrt (1 + μ * s) *
Real.exp (-μ * s / 2)`. -/
def jointMomentumEnvelope (μ s : ℝ) : ℝ :=
  (128 / s ^ 4) * (1 + μ * s) * Real.sqrt (1 + μ * s) * Real.exp (-μ * s / 2)

theorem joint_fixed_polydisc_separation {s : ℝ} (hs : 0 < s) :
    8 * Real.sqrt 3 * (s / 100) ≤ s := by
  have h3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  nlinarith

theorem joint_scaled_coordinate_mem {s : ℝ} (hs : 0 < s)
    {z : Fin 6 → ℂ} (hz : z ∈ coordinateClosedPolydisc 6 (1 / 100)) :
    (fun j => (s : ℂ) * z j) ∈ coordinateClosedPolydisc 6 (s / 100) := by
  intro j
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have h := mul_le_mul_of_nonneg_left (hz j) hs.le
  nlinarith

theorem joint_kernel_exponential_le {μ s : ℝ} (hμ : 0 < μ) (hs : 0 < s) :
    Real.exp (-μ * s + 4 * μ * Real.sqrt 3 * (s / 100)) ≤
      Real.exp (-μ * s / 2) := by
  apply Real.exp_le_exp.mpr
  have h3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have h := mul_le_mul_of_nonneg_left h3 (show 0 ≤ μ * s by positivity)
  nlinarith

theorem jointNormalizedFieldKernel_differentiable {μ s : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (z : Fin 6 → ℂ)
    (hz : z ∈ coordinateClosedPolydisc 6 (1 / 100)) :
    DifferentiableAt ℂ (jointNormalizedFieldKernel μ s) z := by
  exact (spatialSixFieldKernel_differentiable hμ hs (by positivity)
    (joint_fixed_polydisc_separation hs) _ (joint_scaled_coordinate_mem hs hz)).comp z
    (by fun_prop)

theorem jointNormalizedMomentumKernel_differentiable {μ s : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (z : Fin 6 → ℂ)
    (hz : z ∈ coordinateClosedPolydisc 6 (1 / 100)) :
    DifferentiableAt ℂ (jointNormalizedMomentumKernel μ s) z := by
  exact (spatialSixMomentumKernel_differentiable hμ hs (by positivity)
    (joint_fixed_polydisc_separation hs) _ (joint_scaled_coordinate_mem hs hz)).comp z
    (by fun_prop)

theorem jointNormalizedFieldKernel_norm_le {μ s : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (z : Fin 6 → ℂ)
    (hz : z ∈ coordinateClosedPolydisc 6 (1 / 100)) :
    ‖jointNormalizedFieldKernel μ s z‖ ≤ jointFieldEnvelope μ s := by
  apply (spatialSixFieldKernel_norm_le hμ hs (by positivity)
    (joint_fixed_polydisc_separation hs) _ (joint_scaled_coordinate_mem hs hz)).trans
  exact mul_le_mul_of_nonneg_left (joint_kernel_exponential_le hμ hs) (by positivity)

theorem jointNormalizedMomentumKernel_norm_le {μ s : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (z : Fin 6 → ℂ)
    (hz : z ∈ coordinateClosedPolydisc 6 (1 / 100)) :
    ‖jointNormalizedMomentumKernel μ s z‖ ≤ jointMomentumEnvelope μ s := by
  apply (spatialSixMomentumKernel_norm_le hμ hs (by positivity)
    (joint_fixed_polydisc_separation hs) _ (joint_scaled_coordinate_mem hs hz)).trans
  exact mul_le_mul_of_nonneg_left (joint_kernel_exponential_le hμ hs) (by positivity)

/-- The literal oriented field polynomial; z contains physical offsets divided by s. -/
def jointOrientedFieldPolynomial (μ s : ℝ) (n : ℕ) (z : Fin 6 → ℂ) : ℂ :=
  selectedCauchyTaylor n (1 / 100) (jointNormalizedFieldKernel μ s) (z 0) (-z 3) z

/-- Joint oriented momentum polynomial defined as `selectedCauchyTaylor n (1 / 100)
(jointNormalizedMomentumKernel μ s) (z 0) (-z 3) z`. -/
def jointOrientedMomentumPolynomial (μ s : ℝ) (n : ℕ) (z : Fin 6 → ℂ) : ℂ :=
  selectedCauchyTaylor n (1 / 100) (jointNormalizedMomentumKernel μ s) (z 0) (-z 3) z

theorem jointOrientedFieldPolynomial_cross_error {μ s δ : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 200)
    (n : ℕ) (z : Fin 6 → ℂ) (hz : ∀ j, ‖z j‖ ≤ δ) :
    ‖jointNormalizedFieldKernel μ s z - jointOrientedFieldPolynomial μ s n z‖ ≤
      jointFieldEnvelope μ s * (576 * (200 * δ) ^ n + 8 * (8 * δ) ^ (2 * n)) := by
  have h := selectedCauchyTaylor_desired_error (n := n) (R := 1 / 100)
    (by norm_num) hδ (by linarith) (by linarith)
    (show 0 ≤ jointFieldEnvelope μ s by unfold jointFieldEnvelope; positivity)
    (jointNormalizedFieldKernel μ s) (jointNormalizedFieldKernel_differentiable hμ hs)
    (jointNormalizedFieldKernel_norm_le hμ hs) (z 0) (-z 3) z (hz 0)
    (by simpa only [norm_neg] using hz 3) hz
  simpa only [jointOrientedFieldPolynomial, show 2 * (δ / (1 / 100 : ℝ)) = 200 * δ by ring] using h

theorem jointOrientedMomentumPolynomial_cross_error {μ s δ : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 200)
    (n : ℕ) (z : Fin 6 → ℂ) (hz : ∀ j, ‖z j‖ ≤ δ) :
    ‖jointNormalizedMomentumKernel μ s z - jointOrientedMomentumPolynomial μ s n z‖ ≤
      jointMomentumEnvelope μ s * (576 * (200 * δ) ^ n + 8 * (8 * δ) ^ (2 * n)) := by
  have h := selectedCauchyTaylor_desired_error (n := n) (R := 1 / 100)
    (by norm_num) hδ (by linarith) (by linarith)
    (show 0 ≤ jointMomentumEnvelope μ s by unfold jointMomentumEnvelope; positivity)
    (jointNormalizedMomentumKernel μ s) (jointNormalizedMomentumKernel_differentiable hμ hs)
    (jointNormalizedMomentumKernel_norm_le hμ hs) (z 0) (-z 3) z (hz 0)
    (by simpa only [norm_neg] using hz 3) hz
  simpa only [jointOrientedMomentumPolynomial, show 2 * (δ /
    (1 / 100 : ℝ)) = 200 * δ by ring] using h

end VacuumBellSeparation
