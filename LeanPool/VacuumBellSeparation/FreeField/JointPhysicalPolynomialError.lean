/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPhysicalCoordinates
public import LeanPool.VacuumBellSeparation.FreeField.JointKernelAnalytic
public import LeanPool.VacuumBellSeparation.Polynomial.JointComponentAnalytic
public import LeanPool.VacuumBellSeparation.Polynomial.ComplexBallDerivativeBounds

/-!
# Physical complex derivative bounds for the actual joint polynomial

The error is formed from the negative cross kernel on the two cross
components, zero on the two same-region components, and the actual
midpoint polynomial. Physical radius-one neighborhoods give derivative
bounds through order four, uniform in mass after the original envelope.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian MvPolynomial Metric

/-- Joint physical polynomial error. -/
def jointPhysicalPolynomialError (F : (Fin 6 → ℂ) → ℂ) (s : ℝ) (n : ℕ)
    (a b : Bool) (w : Fin 6 → ℂ) : ℂ :=
  jointComponentKernel F a b (jointPhysicalMidpoint s w) -
    eval (jointPhysicalMidpoint s w) (jointMidpointPolynomial F n)

theorem jointPhysicalPolynomialError_ball {s M : ℝ} (hs : 600 ≤ s) (hM : 0 ≤ M)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖F z‖ ≤ M)
    (n : ℕ) (a b : Bool) (w : Fin 6 → ℂ) (hw : InPhysicalJointComponent a b s 2 w) :
    AnalyticOnNhd ℂ (jointPhysicalPolynomialError F s n a b) (ball w 1) ∧
      ∀ y ∈ ball w 1, ‖jointPhysicalPolynomialError F s n a b y‖ ≤
        1168 * M * (78643200 / s) ^ n := by
  have hs₀ : 0 < s := by linarith
  have hδ : 0 ≤ 3 / s := by positivity
  have hsmall : 3 / s ≤ 1 / 200 := (div_le_iff₀ hs₀).mpr (by linarith)
  have hz (y : Fin 6 → ℂ) (hy : y ∈ ball w 1) :
      InJointComponent a b (3 / s) (jointPhysicalMidpoint s y) :=
    (hw.ball_one hy).normalize hs₀
  constructor
  · intro y hy
    exact ((jointComponentKernel_analyticAt (by linarith) F hF a b
      (jointPhysicalMidpoint s y) (hz y hy)).sub
        (jointMidpointPolynomial_analyticAt F n (jointPhysicalMidpoint s y))).comp
          (jointPhysicalMidpoint_analyticAt s y)
  · intro y hy
    have h := jointMidpointPolynomial_component_error hM hδ hsmall F
      (fun z hz => (hF z hz).differentiableAt) hbound n a b
      (jointPhysicalMidpoint s y) (hz y hy)
    simpa only [jointPhysicalPolynomialError,
      show (26214400 : ℝ) * (3 / s) = 78643200 / s by ring] using h

/-- Literal physical complex Fréchet derivatives, with no assumed differentiated error. -/
theorem jointPhysicalPolynomialError_derivative {s M : ℝ} (hs : 600 ≤ s) (hM : 0 ≤ M)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖F z‖ ≤ M)
    (n : ℕ) (a b : Bool) (w : Fin 6 → ℂ) (hw : InPhysicalJointComponent a b s 2 w)
    {k : ℕ} (hk : k ≤ 4) :
    ‖iteratedFDeriv ℂ k (jointPhysicalPolynomialError F s n a b) w‖ ≤
      11680000 * M * (78643200 / s) ^ n := by
  have h := jointPhysicalPolynomialError_ball hs hM F hF hbound n a b w hw
  have hs₀ : 0 < s := by linarith
  exact (norm_iteratedFDeriv_le_four (by positivity) h.1 h.2 hk).trans_eq (by ring)

theorem jointFieldPolynomialError_derivative {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
    (n : ℕ) (a b : Bool) (w : Fin 6 → ℂ) (hw : InPhysicalJointComponent a b s 2 w)
    {k : ℕ} (hk : k ≤ 4) :
    ‖iteratedFDeriv ℂ k
      (jointPhysicalPolynomialError (jointNormalizedFieldKernel μ s) s n a b) w‖ ≤
      11680000 * jointFieldEnvelope μ s * (78643200 / s) ^ n := by
  have hs₀ : 0 < s := by linarith
  exact jointPhysicalPolynomialError_derivative hs
    (by unfold jointFieldEnvelope; positivity) (jointNormalizedFieldKernel μ s)
    (jointNormalizedFieldKernel_analyticAt hμ hs₀)
    (jointNormalizedFieldKernel_norm_le hμ hs₀) n a b w hw hk

theorem jointMomentumPolynomialError_derivative {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
    (n : ℕ) (a b : Bool) (w : Fin 6 → ℂ) (hw : InPhysicalJointComponent a b s 2 w)
    {k : ℕ} (hk : k ≤ 4) :
    ‖iteratedFDeriv ℂ k
      (jointPhysicalPolynomialError (jointNormalizedMomentumKernel μ s) s n a b) w‖ ≤
      11680000 * jointMomentumEnvelope μ s * (78643200 / s) ^ n := by
  have hs₀ : 0 < s := by linarith
  exact jointPhysicalPolynomialError_derivative hs
    (by unfold jointMomentumEnvelope; positivity) (jointNormalizedMomentumKernel μ s)
    (jointNormalizedMomentumKernel_analyticAt hμ hs₀)
    (jointNormalizedMomentumKernel_norm_le hμ hs₀) n a b w hw hk

end VacuumBellSeparation
