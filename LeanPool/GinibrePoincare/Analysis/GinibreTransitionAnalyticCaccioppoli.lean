/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticCaccioppoli.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticWeakCore

/-! Quantitative energy control from the actual localized weak resolvent test
identity. The gradient need only be square-integrable after the cutoff. -/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem localResolventCaccioppoli_energy_bound {Ω E : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure Ω) (U F : Ω → ℝ) (G H : Ω → E)
    (hU : MemLp U 2 μ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (hH : MemLp H 2 μ)
    (ℓ c : ℝ) (hℓ : 0 < ℓ) (hc : 0 < c)
    (heq : ℓ * (∫ x, (U x) ^ 2 ∂μ) + c * (∫ x, ‖G x‖ ^ 2 ∂μ) =
      (∫ x, F x * U x ∂μ) - 2 * c * (∫ x, inner ℝ (G x) (H x) ∂μ)) :
    (ℓ/2)*(∫ x, (U x)^2 ∂μ)+(c/2)*(∫ x, ‖G x‖^2 ∂μ) ≤
      (1/(2*ℓ))*(∫ x, (F x)^2 ∂μ)+2*c*(∫ x, ‖H x‖^2 ∂μ) := by
  have hFU : Integrable (fun x => F x*U x) μ := hF.integrable_mul hU
  have hGH : Integrable (fun x => inner ℝ (G x) (H x)) μ := (hG.norm.integrable_mul hH.norm).mono'
      (hG.aestronglyMeasurable.inner hH.aestronglyMeasurable)
    (ae_of_all μ fun x => norm_inner_le_norm (G x) (H x))
  have hyoung (x : Ω) : F x*U x ≤ (ℓ/2)*(U x)^2+(1/(2*ℓ))*(F x)^2 := by
    have hh := sq_nonneg (ℓ*U x-F x)
    have hden : 0 < 2*ℓ := by positivity
    have hr : (ℓ/2)*(U x)^2+(1/(2*ℓ))*(F x)^2 =
        (ℓ^2*(U x)^2+(F x)^2)/(2*ℓ) := by field_simp
    rw [hr]
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hcross (x : Ω) : -2*c*inner ℝ (G x) (H x) ≤
      (c/2)*‖G x‖^2+2*c*‖H x‖^2 := by
    have hh : -inner ℝ (G x) (H x) ≤ ‖G x‖*‖H x‖ :=
      (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
    nlinarith [sq_nonneg (‖G x‖-2*‖H x‖)]
  have h1 := integral_mono hFU
    ((hU.integrable_sq.const_mul (ℓ/2)).add (hF.integrable_sq.const_mul (1/(2*ℓ)))) hyoung
  have h2 := integral_mono (hGH.const_mul (-2*c))
    ((hG.norm.integrable_sq.const_mul (c/2)).add (hH.norm.integrable_sq.const_mul (2*c))) hcross
  have hi1 := integral_add (hU.integrable_sq.const_mul (ℓ/2)) (hF.integrable_sq.const_mul (1/(2*ℓ)))
  have hi2 := integral_add (hG.norm.integrable_sq.const_mul (c/2)) (hH.norm.integrable_sq.const_mul
      (2*c))
  simp only [Pi.add_apply] at h1 h2 hi1 hi2
  rw [hi1, integral_const_mul, integral_const_mul] at h1
  rw [integral_const_mul, hi2, integral_const_mul, integral_const_mul] at h2
  linarith

end
end GinibrePoincare
