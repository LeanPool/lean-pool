/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebIntegralCS.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebMatrix
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.QuadraticDiscriminant
/-!
# Correspondence Brascamp Lieb integral CS

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_integral_inverse_hessian`.
-/

@[expose] public section
open MeasureTheory
open scoped Matrix
namespace GinibrePoincare
noncomputable section

/-- Integral Cauchy–Schwarz from variable quadratic forms. This avoids
any uniform bound on the Hessian or its inverse. -/
theorem correspondenceBrascampLieb_integral_quadratic
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (a b h : X → ℝ)
    (ha : Integrable a μ) (hb : Integrable b μ) (hh : Integrable h μ)
    (ha0 : ∀ᵐ x ∂μ, 0 ≤ a x) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hcs : ∀ᵐ x ∂μ, h x ^ 2 ≤ a x * b x) :
    (∫ x, h x ∂μ) ^ 2 ≤ (∫ x, a x ∂μ) * (∫ x, b x ∂μ) := by
  have hy (t : ℝ) :
      2 * t * (∫ x, h x ∂μ) ≤ (∫ x, a x ∂μ) + t ^ 2 * (∫ x, b x ∂μ) := by
    have hp : ∀ᵐ x ∂μ, (2*t)*h x ≤ a x + t^2*b x := by
      filter_upwards [ha0, hb0, hcs] with x hax hbx hcx
      have hs : (t*h x)^2 ≤ a x*(t^2*b x) := by
        nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hcx)]
      have he := two_mul_le_add_of_sq_le_mul hax
        (mul_nonneg (sq_nonneg t) hbx) hs
      nlinarith
    have he := integral_mono_ae (hh.const_mul (2*t))
      (ha.add (hb.const_mul (t^2))) hp
    change (∫ x, (2*t)*h x ∂μ) ≤ ∫ x, a x + t^2*b x ∂μ at he
    rw [integral_add ha (hb.const_mul (t^2)), integral_const_mul,
      integral_const_mul] at he
    exact he
  have hd := discrim_le_zero (a := ∫ x, b x ∂μ)
    (b := -2*(∫ x, h x ∂μ)) (c := ∫ x, a x ∂μ) (fun t => by
      have ht := hy t
      nlinarith)
  unfold discrim at hd
  nlinarith

theorem correspondenceBrascampLieb_integral_inverse_hessian
    {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure X) (H : X → Matrix ι ι ℝ) (a b : X → ι → ℝ)
    (hH : ∀ x, (H x).PosDef)
    (ha : Integrable (fun x => a x ⬝ᵥ (H x)⁻¹ *ᵥ a x) μ)
    (hb : Integrable (fun x => b x ⬝ᵥ H x *ᵥ b x) μ)
    (hh : Integrable (fun x => a x ⬝ᵥ b x) μ) :
    (∫ x, a x ⬝ᵥ b x ∂μ)^2 ≤
      (∫ x, a x ⬝ᵥ (H x)⁻¹ *ᵥ a x ∂μ) *
      (∫ x, b x ⬝ᵥ H x *ᵥ b x ∂μ) := by
  apply correspondenceBrascampLieb_integral_quadratic μ _ _ _ ha hb hh
  · exact Filter.Eventually.of_forall fun x => by
      simpa only [star_trivial] using
        (hH x).posSemidef.inv.dotProduct_mulVec_nonneg (a x)
  · exact Filter.Eventually.of_forall fun x => by
      simpa only [star_trivial] using (hH x).posSemidef.dotProduct_mulVec_nonneg (b x)
  · exact Filter.Eventually.of_forall fun x =>
      correspondenceBrascampLieb_inverse_cauchy_schwarz (H x) (hH x) (a x) (b x)

end
end GinibrePoincare
