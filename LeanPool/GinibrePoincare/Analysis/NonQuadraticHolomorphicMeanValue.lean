/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticHolomorphicMeanValue.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticDbarMollification
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! # Radial convolution mean values for entire functions -/

@[expose] public section
open MeasureTheory Set Real
open scoped ContDiff Convolution
namespace GinibrePoincare
noncomputable section

private theorem complex_polar_integrable (F : ℂ → ℂ) (hFc : Continuous F)
    (hF : Integrable F volume) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
      polarCoord.target volume := by
  have hpc : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  refine ⟨(continuous_fst.smul (hFc.comp hpc)).aestronglyMeasurable, ?_⟩
  have he : (fun p : ℝ × ℝ => ‖p.1 • F (Complex.polarCoord.symm p)‖ₑ) =ᵐ[volume.restrict
      polarCoord.target]
      (fun p => ENNReal.ofReal p.1 • ‖F (Complex.polarCoord.symm p)‖ₑ) := by
    filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
    rw [enorm_smul, Real.enorm_eq_ofReal hp.1.le]
    rfl
  change (∫⁻ p in polarCoord.target, ‖p.1 • F (Complex.polarCoord.symm p)‖ₑ) < ⊤
  rw [lintegral_congr_ae he, Complex.lintegral_comp_polarCoord_symm (fun w => ‖F w‖ₑ)]
  exact hF.hasFiniteIntegral

/-- The complete angular mean value in the same angle interval used by
Mathlib's planar polar-coordinate map. -/
theorem holomorphic_polar_angle_integral (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (c : ℂ) (r : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (c - Complex.polarCoord.symm (r, θ))) =
      (2 * Real.pi) • f c := by
  have hmean : circleAverage f c (-r) = f c := hf.diffContOnCl.circleAverage
  have hshift := circleAverage_eq_integral_add (f := f) (c := c) (R := -r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right (f := fun θ => f (circleMap c (-r) θ))
      (-Real.pi)] at hshift
  have hb : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [hb, zero_add] at hshift
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo] at hshift
  have hp (θ : ℝ) : circleMap c (-r) θ = c - Complex.polarCoord.symm (r, θ) := by
    simp only [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
    push_cast
    ring
  simp_rw [hp] at hshift
  rw [hmean] at hshift
  have he := congrArg (fun z : ℂ => (2 * Real.pi) • z) hshift
  simpa only [smul_smul, mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul] using
      he.symm

/-- Every radial compact continuous averaging kernel reproduces an entire
function up to the kernel's actual integral. -/
theorem radial_integral_holomorphic_mean_value (k : ℂ → ℝ)
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hkr : ∀ z, k z = k (‖z‖ : ℂ)) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (c : ℂ) :
    (∫ w, k w • f (c - w)) = (∫ w, k w) • f c := by
  let F := fun w => k w • f (c - w)
  let G := fun w => k w • f c
  have hFc : Continuous F := hk.smul (hf.continuous.comp (continuous_const.sub continuous_id))
  have hGc : Continuous G := hk.smul continuous_const
  have hFi : Integrable F volume := hFc.integrable_of_hasCompactSupport hkc.smul_right
  have hGi : Integrable G volume := hGc.integrable_of_hasCompactSupport hkc.smul_right
  have hFp := complex_polar_integrable F hFc hFi
  have hGp := complex_polar_integrable G hGc hGi
  have hrad (r : ℝ) (hr : 0 < r) (θ : ℝ) : k (Complex.polarCoord.symm (r, θ)) = k (r : ℂ) := by
    rw [hkr, Complex.norm_polarCoord_symm, abs_of_pos hr]
  have hang (r : ℝ) (hr : 0 < r) :
      (∫ θ in Ioo (-Real.pi) Real.pi, r • F (Complex.polarCoord.symm (r, θ))) =
        ∫ θ in Ioo (-Real.pi) Real.pi, r • G (Complex.polarCoord.symm (r, θ)) := by
    have hcst : (∫ θ in Ioo (-Real.pi) Real.pi, f c) = (2 * Real.pi) • f c := by
      simpa only using holomorphic_polar_angle_integral (fun _ => f c) (differentiable_const (f c))
          c r
    change (∫ θ in Ioo (-Real.pi) Real.pi, r • (k (Complex.polarCoord.symm (r, θ)) •
      f (c - Complex.polarCoord.symm (r, θ)))) =
      ∫ θ in Ioo (-Real.pi) Real.pi, r • (k (Complex.polarCoord.symm (r, θ)) • f c)
    simp_rw [hrad r hr, smul_smul]
    rw [integral_smul, integral_smul, holomorphic_polar_angle_integral f hf c r, hcst]
  calc
    (∫ w, k w • f (c - w)) = ∫ w, F w := rfl
    _ = ∫ p in polarCoord.target, p.1 • F (Complex.polarCoord.symm p) :=
      (Complex.integral_comp_polarCoord_symm F).symm
    _ = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        r • F (Complex.polarCoord.symm (r, θ)) := by
      rw [polarCoord_target]
      exact setIntegral_prod (μ := volume) (ν := volume) _ hFp
    _ = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        r • G (Complex.polarCoord.symm (r, θ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact hang r hr
    _ = ∫ p in polarCoord.target, p.1 • G (Complex.polarCoord.symm p) := by
      rw [polarCoord_target]
      exact (setIntegral_prod (μ := volume) (ν := volume) _ hGp).symm
    _ = ∫ w, G w := Complex.integral_comp_polarCoord_symm G
    _ = (∫ w, k w) • f c := integral_smul_const _ _

/-- Entire mean value for arbitrary continuous radial integrable weights. -/
theorem radial_integral_holomorphic_mean_value_of_integrable (k : ℂ → ℝ)
    (hk : Continuous k) (hki : Integrable k volume)
    (hkr : ∀ z, k z = k (‖z‖ : ℂ)) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (c : ℂ)
    (hFi : Integrable (fun w => k w • f (c - w)) volume) :
    (∫ w, k w • f (c - w)) = (∫ w, k w) • f c := by
  let F := fun w => k w • f (c - w)
  let G := fun w => k w • f c
  have hFc : Continuous F := hk.smul (hf.continuous.comp (continuous_const.sub continuous_id))
  have hGc : Continuous G := hk.smul continuous_const
  have hGi : Integrable G volume := hki.smul_const (f c)
  have hFp := complex_polar_integrable F hFc hFi
  have hGp := complex_polar_integrable G hGc hGi
  have hrad (r : ℝ) (hr : 0 < r) (θ : ℝ) : k (Complex.polarCoord.symm (r, θ)) = k (r : ℂ) := by
    rw [hkr, Complex.norm_polarCoord_symm, abs_of_pos hr]
  have hang (r : ℝ) (hr : 0 < r) :
      (∫ θ in Ioo (-Real.pi) Real.pi, r • F (Complex.polarCoord.symm (r, θ))) =
        ∫ θ in Ioo (-Real.pi) Real.pi, r • G (Complex.polarCoord.symm (r, θ)) := by
    have hcst : (∫ θ in Ioo (-Real.pi) Real.pi, f c) = (2 * Real.pi) • f c := by
      simpa only using holomorphic_polar_angle_integral (fun _ => f c) (differentiable_const (f c))
          c r
    change (∫ θ in Ioo (-Real.pi) Real.pi, r • (k (Complex.polarCoord.symm (r, θ)) •
      f (c - Complex.polarCoord.symm (r, θ)))) =
      ∫ θ in Ioo (-Real.pi) Real.pi, r • (k (Complex.polarCoord.symm (r, θ)) • f c)
    simp_rw [hrad r hr, smul_smul]
    rw [integral_smul, integral_smul, holomorphic_polar_angle_integral f hf c r, hcst]
  calc
    (∫ w, k w • f (c - w)) = ∫ w, F w := rfl
    _ = ∫ p in polarCoord.target, p.1 • F (Complex.polarCoord.symm p) :=
      (Complex.integral_comp_polarCoord_symm F).symm
    _ = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        r • F (Complex.polarCoord.symm (r, θ)) := by
      rw [polarCoord_target]
      exact setIntegral_prod (μ := volume) (ν := volume) _ hFp
    _ = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        r • G (Complex.polarCoord.symm (r, θ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact hang r hr
    _ = ∫ p in polarCoord.target, p.1 • G (Complex.polarCoord.symm p) := by
      rw [polarCoord_target]
      exact (setIntegral_prod (μ := volume) (ν := volume) _ hGp).symm
    _ = ∫ w, G w := Complex.integral_comp_polarCoord_symm G
    _ = (∫ w, k w) • f c := integral_smul_const _ _

/-- Genuine entire-function reproduction by normalized radial smooth convolution. -/
theorem radial_convolution_holomorphic_eq (k : ℂ → ℝ)
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hkr : ∀ z, k z = k (‖z‖ : ℂ)) (hkn : (∫ w, k w) = 1)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) = f := by
  funext c
  rw [convolution_lsmul]
  have he := radial_integral_holomorphic_mean_value k hk hkc hkr f hf c
  simpa only [hkn, one_smul] using he

end
end GinibrePoincare
