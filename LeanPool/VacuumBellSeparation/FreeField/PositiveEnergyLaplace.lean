/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PositiveEnergyPhase
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Actual positive-energy Laplace transforms, including boundary derivatives

The transform is the literal Bochner integral. Integrability of the
amplitude and its first energy moment suffice for a complex derivative
within the closed upper half-plane, and hence holomorphy in its interior.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Set
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Positive energy Laplace given by `∫ a, positiveEnergyPhase (ω a) z * A a ∂μ`. -/
noncomputable def positiveEnergyLaplace (μ : Measure α) (ω : α → ℝ)
    (A : α → ℂ) (z : ℂ) : ℂ :=
  ∫ a, positiveEnergyPhase (ω a) z * A a ∂μ

theorem aestronglyMeasurable_positiveEnergyPhase
    {ω : α → ℝ} (hω : AEStronglyMeasurable ω μ) (z : ℂ) :
    AEStronglyMeasurable (fun a => positiveEnergyPhase (ω a) z) μ := by
  have hc : Continuous (fun r : ℝ => positiveEnergyPhase r z) := by
    unfold positiveEnergyPhase
    fun_prop
  exact hc.comp_aestronglyMeasurable hω

theorem integrable_positiveEnergyLaplace_integrand
    {ω : α → ℝ} {A : α → ℂ} (hω : AEStronglyMeasurable ω μ)
    (hω₀ : ∀ a, 0 ≤ ω a) (hA : Integrable A μ) {z : ℂ} (hz : 0 ≤ z.im) :
    Integrable (fun a => positiveEnergyPhase (ω a) z * A a) μ := by
  apply hA.norm.mono'
  · exact (aestronglyMeasurable_positiveEnergyPhase hω z).mul hA.aestronglyMeasurable
  · exact Eventually.of_forall fun a => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_positiveEnergyPhase_le_one (hω₀ a) hz)

theorem integrable_positiveEnergyLaplace_derivative
    {ω : α → ℝ} {A : α → ℂ} (hω : AEStronglyMeasurable ω μ)
    (hω₀ : ∀ a, 0 ≤ ω a) (hA : AEStronglyMeasurable A μ)
    (hωA : Integrable (fun a => ω a * ‖A a‖) μ) {z : ℂ} (hz : 0 ≤ z.im) :
    Integrable (fun a => positiveEnergyPhase (ω a) z * (Complex.I * (ω a : ℂ)) * A a) μ := by
  apply hωA.mono'
  · exact ((aestronglyMeasurable_positiveEnergyPhase hω z).mul
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable hω).const_mul Complex.I)).mul hA
  · exact Eventually.of_forall fun a => by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hω₀ a)]
      calc
        _ = ‖positiveEnergyPhase (ω a) z‖ * (ω a * ‖A a‖) := by ring
        _ ≤ _ := mul_le_of_le_one_left (mul_nonneg (hω₀ a) (norm_nonneg _))
          (norm_positiveEnergyPhase_le_one (hω₀ a) hz)

theorem hasDerivWithinAt_positiveEnergyLaplace
    {ω : α → ℝ} {A : α → ℂ} (hω : AEStronglyMeasurable ω μ)
    (hω₀ : ∀ a, 0 ≤ ω a) (hA : Integrable A μ)
    (hωA : Integrable (fun a => ω a * ‖A a‖) μ) {z : ℂ} (hz : 0 ≤ z.im) :
    HasDerivWithinAt (positiveEnergyLaplace μ ω A)
      (∫ a, positiveEnergyPhase (ω a) z * (Complex.I * (ω a : ℂ)) * A a ∂μ)
      {w : ℂ | 0 ≤ w.im} z := by
  apply hasDerivWithinAt_integral_of_dominated_slope
    (F := fun w a => positiveEnergyPhase (ω a) w * A a)
    (D := fun a => positiveEnergyPhase (ω a) z * (Complex.I * (ω a : ℂ)) * A a)
    (s := {w : ℂ | 0 ≤ w.im}) (z₀ := z) (hz₀ := hz)
    (B := fun a => 2 * (ω a * ‖A a‖))
  · intro w hw
    exact integrable_positiveEnergyLaplace_integrand hω hω₀ hA hw
  · intro a
    exact ((hasDerivAt_positiveEnergyPhase (ω a) z).mul_const (A a)).hasDerivWithinAt
  · exact hωA.const_mul 2
  · intro w hw a
    rw [← sub_mul, norm_mul]
    calc
      _ ≤ (2 * ω a * ‖w - z‖) * ‖A a‖ :=
        mul_le_mul_of_nonneg_right (norm_positiveEnergyPhase_sub_le (hω₀ a) hw hz)
          (norm_nonneg _)
      _ = _ := by ring

theorem hasDerivAt_positiveEnergyLaplace
    {ω : α → ℝ} {A : α → ℂ} (hω : AEStronglyMeasurable ω μ)
    (hω₀ : ∀ a, 0 ≤ ω a) (hA : Integrable A μ)
    (hωA : Integrable (fun a => ω a * ‖A a‖) μ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (positiveEnergyLaplace μ ω A)
      (∫ a, positiveEnergyPhase (ω a) z * (Complex.I * (ω a : ℂ)) * A a ∂μ) z := by
  apply (hasDerivWithinAt_positiveEnergyLaplace hω hω₀ hA hωA hz.le).hasDerivAt
  exact Filter.mem_of_superset
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz) (fun w (h :
      (0 : ℝ) < w.im) => show w ∈ {w : ℂ | 0 ≤ w.im} from h.le)

theorem analyticOnNhd_positiveEnergyLaplace
    {ω : α → ℝ} {A : α → ℂ} (hω : AEStronglyMeasurable ω μ)
    (hω₀ : ∀ a, 0 ≤ ω a) (hA : Integrable A μ)
    (hωA : Integrable (fun a => ω a * ‖A a‖) μ) :
    AnalyticOnNhd ℂ (positiveEnergyLaplace μ ω A) {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_im)
  intro z hz
  exact (hasDerivAt_positiveEnergyLaplace hω hω₀ hA hωA hz).differentiableAt.differentiableWithinAt

end VacuumBellSeparation
