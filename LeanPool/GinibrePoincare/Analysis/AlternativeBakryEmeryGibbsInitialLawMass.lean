/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsInitialLawMass.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinGlobal
public import LeanPool.GinibrePoincare.Analysis.BakryEmeryRegularizationVolume
/-!
# Alternative Bakry Emery Gibbs initial law mass

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryStrongConvex_gibbs_probability`.
-/

@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem bakryEmeryStrongConvex_quadratic_lower_bound (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2)) (x : E) :
    κ/4*‖x‖^2+W 0-‖fderiv ℝ W 0‖^2/κ ≤ W x := by
  have hD := ((hW.differentiable (by norm_num)) (0 : E)).hasFDerivAt.sub
    ((hasStrictFDerivAt_norm_sq (0 : E)).hasFDerivAt.const_mul (κ/2))
  have hs := bakryEmery_convex_support hc 0 x hD.differentiableAt
  change (fderiv ℝ (W - fun y => κ/2*‖y‖^2) 0) (x-0) ≤ _ at hs
  rw [hD.fderiv] at hs
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, inner_zero_left,
      two_smul,
    mul_zero, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hs
  have hd : -(‖fderiv ℝ W 0‖*‖x‖) ≤ fderiv ℝ W 0 x := by
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using (fderiv ℝ W 0).le_opNorm x)).1
  have hm := mul_le_mul_of_nonneg_left hs hκ.le
  have hh := mul_le_mul_of_nonneg_left hd hκ.le
  have hcancel : κ*(‖fderiv ℝ W 0‖^2/κ) = ‖fderiv ℝ W 0‖^2 := mul_div_cancel₀ _ hκ.ne'
  apply (mul_le_mul_iff_right₀ hκ).mp
  nlinarith [sq_nonneg (κ*‖x‖/2-‖fderiv ℝ W 0‖)]

omit [CompleteSpace E] in
theorem bakryEmeryStrongConvex_density_integrable (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2)) :
    Integrable (fun x => Real.exp (-W x)) volume := by
  have hg := bakryEmery_gaussian_majorant_integrable (E := E) (κ/4) (by positivity)
  apply (hg.const_mul (Real.exp (‖fderiv ℝ W 0‖^2/κ-W 0))).mono
    (Real.continuous_exp.comp hW.continuous.neg).aestronglyMeasurable
  filter_upwards [] with x
  change ‖Real.exp (-W x)‖ ≤ ‖Real.exp (‖fderiv ℝ W 0‖^2/κ-W 0)*Real.exp (-(κ/4)*‖x‖^2)‖
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := bakryEmeryStrongConvex_quadratic_lower_bound W κ hκ hW hc x
  linarith

omit [CompleteSpace E] in
theorem bakryEmeryStrongConvex_gibbs_probability (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2)) :
    IsProbabilityMeasure (bakryEmeryNormalizedGibbs volume W) :=
  bakryEmeryNormalizedGibbs_probability volume W hW.continuous
    (bakryEmeryStrongConvex_density_integrable W κ hκ hW hc)

end
end GinibrePoincare
