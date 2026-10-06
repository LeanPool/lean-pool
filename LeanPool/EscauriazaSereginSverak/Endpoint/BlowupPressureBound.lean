/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSliceBound

/-!
# Blowup Pressure Bound

Pressure bounds and convergence estimates for the rescaled sequence.
-/

public section

open MeasureTheory Filter CKN.Foundation.Parabolic
open scoped ENNReal
namespace ESS

/-- The global `L^(3/2)` pressure norm is invariant under positive spatial
Navier–Stokes rescaling. -/
theorem blowup_rescaled_pressureSlice_eLpNorm_threeHalves_eq
    (f : Vec3 → ℝ)
    (hf : AEStronglyMeasurable f (volume : Measure Vec3))
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r) :
    eLpNorm (fun x => r ^ 2 * f (x₀ + r • x)) (3 / 2 : ℝ≥0∞)
      (volume : Measure Vec3) =
    eLpNorm f (3 / 2 : ℝ≥0∞) (volume : Measure Vec3) := by
  let a : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 3)
  have hmap : Measure.map (CKN.scalingSpace r x₀) volume =
      a • (volume : Measure Vec3) := CKN.map_scalingSpace r hr x₀
  have hfa : AEStronglyMeasurable f
      (Measure.map (CKN.scalingSpace r x₀) volume) := by
    rw [hmap]
    exact hf.mono_ac Measure.smul_absolutelyContinuous
  have hscaleMeas : Measurable (CKN.scalingSpace r x₀) := by
    unfold CKN.scalingSpace
    fun_prop
  have hcomp : AEStronglyMeasurable (f ∘ CKN.scalingSpace r x₀)
      (volume : Measure Vec3) :=
    hfa.comp_aemeasurable hscaleMeas.aemeasurable
  have hscaled : AEStronglyMeasurable
      (fun x => r ^ 2 * f (x₀ + r • x))
      (volume : Measure Vec3) := by
    simpa only [Function.comp_def, CKN.scalingSpace] using
      hcomp.const_mul (r ^ 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ⊤) hscaled,
    eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ⊤) hf]
  simp only [Real.enorm_eq_ofReal_abs]
  have hm := congrArg (fun a : ℝ≥0∞ => a ^ (2 / 3 : ℝ))
    (blowupPressureSlice_mass_eq f hf x₀ r hr)
  convert hm using 1 <;> norm_num

end ESS
