/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscCauchyCoefficients
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual product-angle integrals on a polydisc boundary

The normalization is the actual product of 2 pi factors. Finite angular
measure and summable uniform bounds justify exchanging any countable
series with this integral. No Cauchy or analytic hypothesis is assumed
in the exchange theorem.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped BigOperators

namespace VacuumBellSeparation.Gaussian

/-- Circle angle measure given by `volume.restrict (Ioc 0 (2 * Real.pi))`. -/
noncomputable def circleAngleMeasure : Measure ℝ :=
  volume.restrict (Ioc 0 (2 * Real.pi))

instance : IsFiniteMeasure circleAngleMeasure := by
  unfold circleAngleMeasure
  infer_instance

/-- Polydisc angle measure given by `Measure.pi (fun _ => circleAngleMeasure)`. -/
noncomputable def polydiscAngleMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => circleAngleMeasure)

instance (n : ℕ) : IsFiniteMeasure (polydiscAngleMeasure n) := by
  unfold polydiscAngleMeasure
  infer_instance

/-- Polydisc boundary point given by `fun j => circleMap 0 R (θ j)`. -/
noncomputable def polydiscBoundaryPoint (n : ℕ) (R : ℝ) (θ : Fin n → ℝ) : Fin n → ℂ :=
  fun j => circleMap 0 R (θ j)

theorem continuous_polydiscBoundaryPoint (n : ℕ) (R : ℝ) :
    Continuous (polydiscBoundaryPoint n R) := by
  unfold polydiscBoundaryPoint
  fun_prop

theorem norm_polydiscBoundaryPoint (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (θ : Fin n → ℝ) (j : Fin n) : ‖polydiscBoundaryPoint n R θ j‖ = R := by
  simp [polydiscBoundaryPoint, abs_of_nonneg hR]

theorem polydiscAngleMeasure_real_univ (n : ℕ) :
    (polydiscAngleMeasure n).real univ = (2 * Real.pi) ^ n := by
  simp [measureReal_def, polydiscAngleMeasure, Measure.pi_univ, circleAngleMeasure,
    Real.volume_Ioc, ENNReal.toReal_ofReal Real.pi_pos.le]

/-- Polydisc angular integral. -/
noncomputable def polydiscAngularIntegral (n : ℕ) (R : ℝ)
    (F : (Fin n → ℂ) → ℂ) : ℂ :=
  ((2 * Real.pi : ℂ) ^ n)⁻¹ *
    ∫ θ, F (polydiscBoundaryPoint n R θ) ∂polydiscAngleMeasure n

theorem polydiscAngularIntegral_norm_le (n : ℕ) {R M : ℝ} (hR : 0 ≤ R)
    (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z, (∀ j, ‖z j‖ = R) → ‖F z‖ ≤ M) :
    ‖polydiscAngularIntegral n R F‖ ≤ M := by
  have hb := norm_integral_le_of_norm_le_const
    (μ := polydiscAngleMeasure n)
    (Filter.Eventually.of_forall (fun θ => hF _ (norm_polydiscBoundaryPoint n hR θ)))
  rw [polydiscAngleMeasure_real_univ] at hb
  have hπ : 0 < 2 * Real.pi := Real.two_pi_pos
  calc
    _ = ((2 * Real.pi) ^ n)⁻¹ *
        ‖∫ θ, F (polydiscBoundaryPoint n R θ) ∂polydiscAngleMeasure n‖ := by
      simp only [polydiscAngularIntegral, norm_mul, norm_inv, norm_pow,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    _ ≤ ((2 * Real.pi) ^ n)⁻¹ * (M * (2 * Real.pi) ^ n) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = M := by field_simp

theorem integrable_polydiscBoundary (n : ℕ) {R M : ℝ} (hR : 0 ≤ R)
    (F : (Fin n → ℂ) → ℂ)
    (hcont : Continuous (fun θ => F (polydiscBoundaryPoint n R θ)))
    (hF : ∀ z, (∀ j, ‖z j‖ = R) → ‖F z‖ ≤ M) :
    Integrable (fun θ => F (polydiscBoundaryPoint n R θ)) (polydiscAngleMeasure n) := by
  apply (integrable_const M).mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun θ => hF _ (norm_polydiscBoundaryPoint n hR θ))

theorem hasSum_polydiscAngularIntegral {ι : Type*} [Countable ι]
    (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (F : ι → (Fin n → ℂ) → ℂ) (G : (Fin n → ℂ) → ℂ) (b : ι → ℝ)
    (hF : ∀ i, Continuous (fun θ => F i (polydiscBoundaryPoint n R θ)))
    (hb : ∀ i z, (∀ j, ‖z j‖ = R) → ‖F i z‖ ≤ b i)
    (hs : Summable b)
    (hlim : ∀ z, (∀ j, ‖z j‖ = R) → HasSum (fun i => F i z) (G z)) :
    HasSum (fun i => polydiscAngularIntegral n R (F i))
      (polydiscAngularIntegral n R G) := by
  have hi := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := polydiscAngleMeasure n) (fun i (_ : Fin n → ℝ) => b i)
    (fun i => (hF i).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall (fun θ => hb i _
      (norm_polydiscBoundaryPoint n hR θ)))
    (Filter.Eventually.of_forall (fun _ => hs)) (integrable_const _)
    (Filter.Eventually.of_forall (fun θ => hlim _
      (norm_polydiscBoundaryPoint n hR θ)))
  exact hi.mul_left _

end VacuumBellSeparation.Gaussian
