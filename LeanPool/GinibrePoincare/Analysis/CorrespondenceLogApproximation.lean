/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceLogApproximation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceLogKernel
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Correspondence log approximation

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `correspondenceLogKernel_test_limit`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory Filter Bornology
open scoped Topology

private theorem logKernel_unit_decay :
    Tendsto (fun z : ℂ => ‖z‖^Module.finrank ℝ ℂ * correspondenceLogKernel 1 z)
      (cobounded ℂ) (𝓝 0) := by
  have hn : Tendsto (fun z : ℂ => ‖z‖^2+1) (cobounded ℂ) atTop :=
    tendsto_atTop_add_const_right _ 1
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_norm_cobounded_atTop)
  have hi := hn.inv_tendsto_atTop.const_mul Real.pi⁻¹
  apply squeeze_zero (fun z => by
    simp only [Complex.finrank_real_complex]
    exact mul_nonneg (sq_nonneg _) (correspondenceLogKernel_nonneg (by norm_num) z))
    (fun z => ?_) (by simpa using hi)
  simp only [Complex.finrank_real_complex, correspondenceLogKernel,
    Complex.normSq_eq_norm_sq]
  have hd : 0 < ‖z‖^2+1 := by positivity
  apply (le_div_iff₀ hd).mpr
  field_simp
  nlinarith [sq_nonneg ‖z‖]

theorem correspondenceLogKernel_scaling {τ : ℝ} (hτ : 0 < τ) (z : ℂ) :
    (Real.sqrt τ)⁻¹^2 * correspondenceLogKernel 1 ((Real.sqrt τ)⁻¹ • z) =
      correspondenceLogKernel τ z := by
  simp only [correspondenceLogKernel, Complex.normSq_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  have hs : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.2 hτ).ne'
  have hτ0 := hτ.ne'
  have hD : ‖z‖^2+τ ≠ 0 := by positivity
  field_simp
  have hs4 : Real.sqrt τ ^ 4 = τ^2 := by
    calc
      _ = (Real.sqrt τ ^ 2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hτ.le]
  simp only [Real.sq_sqrt hτ.le]
  ring

/-- The regularized Laplacian kernels converge to the actual point mass against
every integrable test continuous at the origin. -/
theorem correspondenceLogKernel_test_limit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (g : ℂ → E) (hg : Integrable g)
    (hc : ContinuousAt g 0) :
    Tendsto (fun τ : ℝ => ∫ z : ℂ, correspondenceLogKernel τ z • g z)
      (𝓝[>] 0) (𝓝 (g 0)) := by
  have hp := tendsto_integral_comp_smul_smul_of_integrable
    (μ := (volume : Measure ℂ))
    (correspondenceLogKernel_nonneg (by norm_num : (0 : ℝ) < 1))
    (correspondenceLogKernel_integral (by norm_num : (0 : ℝ) < 1))
    logKernel_unit_decay hg hc
  have hs : Tendsto (fun τ : ℝ => (Real.sqrt τ)⁻¹) (𝓝[>] 0) atTop := by
    have h := tendsto_rpow_neg_nhdsGT_zero (by norm_num : -(1/2 : ℝ) < 0)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    simp [Real.sqrt_eq_rpow, Real.rpow_neg hτ.le]
  have h := hp.comp hs
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Complex.finrank_real_complex]
  rw [correspondenceLogKernel_scaling hτ z]

end
end GinibrePoincare

