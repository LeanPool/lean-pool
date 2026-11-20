/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceLogKernel.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceLogRadial
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-!
# Correspondence log kernel

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `correspondenceLogKernel_integrable`, `correspondenceLogKernel_integral`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory Set
open scoped ENNReal

/-- The genuine normalized regularized planar logarithmic Laplacian. -/
def correspondenceLogKernel (τ : ℝ) (z : ℂ) : ℝ :=
  τ/(Real.pi*(Complex.normSq z+τ)^2)

theorem correspondenceLogKernel_nonneg {τ : ℝ} (hτ : 0 < τ) (z : ℂ) :
    0 ≤ correspondenceLogKernel τ z := by unfold correspondenceLogKernel; positivity

theorem correspondenceLogKernel_continuous {τ : ℝ} (hτ : 0 < τ) :
    Continuous (correspondenceLogKernel τ) := by
  unfold correspondenceLogKernel
  apply continuous_const.div
    (continuous_const.mul ((Complex.continuous_normSq.add continuous_const).pow 2))
  intro z
  have hn := Complex.normSq_nonneg z
  exact mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 (ne_of_gt (by linarith : 0 < Complex.normSq
                                                                   z+τ)))

theorem correspondenceLogKernel_lintegral {τ : ℝ} (hτ : 0 < τ) :
    (∫⁻ z : ℂ, ENNReal.ofReal (correspondenceLogKernel τ z)) = 1 := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  change (∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * ENNReal.ofReal (correspondenceLogKernel τ (Complex.polarCoord.symm p))) = 1
  have heq : (∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * ENNReal.ofReal (correspondenceLogKernel τ (Complex.polarCoord.symm p))) =
      ∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (correspondenceLogRadial τ p.1) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
    rw [← ENNReal.ofReal_mul hp.1.le]
    congr 1
    simp only [correspondenceLogKernel, correspondenceLogRadial,
      Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, sq_abs]
    ring
  rw [heq, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hrcont : Continuous (correspondenceLogRadial τ) := by
    unfold correspondenceLogRadial
    apply (continuous_const.mul continuous_id).div
      (continuous_const.mul (((continuous_id.pow 2).add continuous_const).pow 2))
    intro r
    change Real.pi*(r^2+τ)^2 ≠ 0
    exact mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 (ne_of_gt (by positivity : 0 < r^2+τ)))
  have hm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (correspondenceLogRadial τ p.1))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    fun_prop
  rw [lintegral_prod _ hm]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  rw [lintegral_mul_const', ← ofReal_integral_eq_lintegral_ofReal
    (correspondenceLogRadial_integrable hτ (le_refl 0))]
  · rw [correspondenceLogRadial_integral hτ (le_refl 0)]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_add, sub_neg_eq_add,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ τ/(2*Real.pi*τ))]
    have heq : τ/(2*Real.pi*τ)*(Real.pi+Real.pi) = 1 := by field_simp; ring
    rw [heq]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := hr.le
    unfold correspondenceLogRadial
    positivity
  · simp

theorem correspondenceLogKernel_integrable {τ : ℝ} (hτ : 0 < τ) :
    Integrable (correspondenceLogKernel τ) := by
  refine ⟨(correspondenceLogKernel_continuous hτ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (correspondenceLogKernel_nonneg hτ)),
    correspondenceLogKernel_lintegral hτ]
  simp

theorem correspondenceLogKernel_integral {τ : ℝ} (hτ : 0 < τ) :
    (∫ z : ℂ, correspondenceLogKernel τ z) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (correspondenceLogKernel_nonneg hτ))
    (correspondenceLogKernel_continuous hτ).aestronglyMeasurable,
    correspondenceLogKernel_lintegral hτ]
  simp

end
end GinibrePoincare

