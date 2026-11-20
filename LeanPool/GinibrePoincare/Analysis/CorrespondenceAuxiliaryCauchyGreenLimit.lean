/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryCauchyGreenLimit.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenRegularized
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Correspondence auxiliary Cauchy Green limit

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `cauchyGreenRegularizedKernel_integral_tendsto`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace GinibrePoincare
noncomputable section

theorem cauchyGreenRegularizedKernel_norm_le (τ : ℝ) (hτ : 0 < τ) (z : ℂ) :
    ‖cauchyGreenRegularizedKernel τ z‖ ≤ ‖cauchyGreenKernel z‖ := by
  by_cases hz : z = 0
  · simp [cauchyGreenRegularizedKernel, cauchyGreenKernel, hz]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hden : 0 < Real.pi*(Complex.normSq z+τ) :=
    mul_pos Real.pi_pos ((Complex.normSq_nonneg z).trans_lt (lt_add_of_pos_right _ hτ))
  have hs : 0 < Complex.normSq z+τ :=
    (Complex.normSq_nonneg z).trans_lt (lt_add_of_pos_right _ hτ)
  simp only [cauchyGreenRegularizedKernel, cauchyGreenKernel, norm_div, norm_mul, norm_inv,
    Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
    abs_of_pos Real.pi_pos]
  rw [div_le_iff₀ hden, Complex.normSq_eq_norm_sq]
  field_simp [hr.ne', Real.pi_ne_zero]
  nlinarith

theorem cauchyGreenRegularizedKernel_tendsto (z : ℂ) :
    Tendsto (fun τ : ℝ => cauchyGreenRegularizedKernel τ z) (𝓝[>] 0)
      (𝓝 (cauchyGreenKernel z)) := by
  by_cases hz : z = 0
  · simp only [hz, cauchyGreenRegularizedKernel, cauchyGreenKernel, map_zero, zero_div, inv_zero,
      mul_zero]
    exact tendsto_const_nhds
  have hden : ((Real.pi*Complex.normSq z : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero (Complex.normSq_pos.mpr hz).ne')
  have hl : Tendsto (fun τ : ℝ => Real.pi*(Complex.normSq z+τ)) (𝓝[>] 0)
      (𝓝 (Real.pi*Complex.normSq z)) := by
    simpa only [add_zero, id_eq] using!
      (((tendsto_const_nhds : Tendsto (fun _ : ℝ => Complex.normSq z) (𝓝[>] 0)
        (𝓝 (Complex.normSq z))).add
        ((tendsto_id : Tendsto (fun τ : ℝ => τ) (𝓝 0) (𝓝 0)).mono_left
          nhdsWithin_le_nhds)).const_mul Real.pi)
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => conj z) (𝓝[>] 0) (𝓝 (conj z))).div
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hl) hden
  have he : cauchyGreenKernel z = conj z / ((Real.pi*Complex.normSq z : ℝ) : ℂ) := by
    rw [cauchyGreenKernel, Complex.inv_def z]
    push_cast
    field_simp
  rw [he]
  simpa only [cauchyGreenRegularizedKernel, Function.comp_def, Pi.div_apply] using! h

/-- Genuine compact-test convergence of the locally integrable singular
Cauchy–Green kernel under positive radial regularization. -/
theorem cauchyGreenRegularizedKernel_integral_tendsto (φ : ℂ → ℂ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Tendsto (fun τ : ℝ => ∫ z : ℂ, cauchyGreenRegularizedKernel τ z * φ z)
      (𝓝[>] 0) (𝓝 (∫ z : ℂ, cauchyGreenKernel z * φ z)) := by
  have hi : Integrable (fun z => ‖cauchyGreenKernel z‖ * ‖φ z‖) volume := by
    have hn : LocallyIntegrable (fun z => ‖cauchyGreenKernel z‖) volume := by
      intro z
      obtain ⟨s, hs, hi⟩ := cauchyGreenKernel_locallyIntegrable z
      exact ⟨s, hs, hi.norm⟩
    simpa only [smul_eq_mul] using hn.integrable_smul_right_of_hasCompactSupport
      hφ.norm (hc.comp_left norm_zero)
  apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖cauchyGreenKernel z‖*‖φ z‖)
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact ((cauchyGreenRegularizedKernel_contDiff τ hτ).continuous.mul hφ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact ae_of_all _ (fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (cauchyGreenRegularizedKernel_norm_le τ hτ z) (norm_nonneg
          _))
  · exact hi
  · exact ae_of_all _ (fun z => (cauchyGreenRegularizedKernel_tendsto z).mul tendsto_const_nhds)

end
end GinibrePoincare
