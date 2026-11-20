/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceLogLimit.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceLogRegularized

/-!
# Correspondence log limit

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `correspondenceLogRegularized_integral_tendsto`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem correspondenceLogRegularized_norm_le (τ : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (z : ℂ) (hz : z ≠ 0) :
    ‖correspondenceLogRegularized τ z‖ ≤ ‖z‖^2 + ‖correspondenceLogPotential z‖ := by
  have hr := norm_pos_iff.mpr hz
  have hp : 0 < Complex.normSq z+τ :=
    (Complex.normSq_nonneg z).trans_lt (lt_add_of_pos_right _ hτ)
  have hl := Real.log_le_log (sq_pos_of_pos hr)
    (show ‖z‖^2 ≤ Complex.normSq z+τ by rw [Complex.normSq_eq_norm_sq]; linarith)
  rw [Real.log_pow] at hl
  have hu := Real.log_le_sub_one_of_pos hp
  simp only [Complex.normSq_eq_norm_sq] at hu
  simp only [Complex.normSq_eq_norm_sq] at hl ⊢
  simp only [correspondenceLogRegularized, correspondenceLogPotential, Real.norm_eq_abs,
      Complex.normSq_eq_norm_sq]
  rw [abs_le]
  constructor
  · have ha := neg_abs_le (Real.log ‖z‖)
    have hs := sq_nonneg ‖z‖
    norm_num at hl
    linarith
  · have ha := abs_nonneg (Real.log ‖z‖)
    have hs := sq_nonneg ‖z‖
    linarith

theorem correspondenceLogRegularized_tendsto (z : ℂ) (hz : z ≠ 0) :
    Tendsto (fun τ : ℝ => correspondenceLogRegularized τ z) (𝓝[>] 0)
      (𝓝 (correspondenceLogPotential z)) := by
  have hl : Tendsto (fun τ : ℝ => Complex.normSq z+τ) (𝓝[>] 0)
      (𝓝 (Complex.normSq z)) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_id : Tendsto (fun τ : ℝ => τ) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds)
  have h := ((Real.continuousAt_log (Complex.normSq_pos.mpr hz).ne').tendsto.comp hl).const_mul (1/2
      : ℝ)
  simpa only [correspondenceLogRegularized, correspondenceLogPotential,
    Complex.normSq_eq_norm_sq, Real.log_pow, Nat.cast_ofNat, one_div, mul_assoc,
    inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul, Function.comp_def, inv_mul_cancel_left₀
        (by norm_num : (2 : ℝ) ≠ 0)] using h

theorem correspondenceLogRegularized_integral_tendsto (θ : ℂ → ℂ)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    Tendsto (fun τ : ℝ => ∫ z : ℂ, (correspondenceLogRegularized τ z : ℂ)*θ z)
      (𝓝[>] 0) (𝓝 (∫ z : ℂ, (correspondenceLogPotential z : ℂ)*θ z)) := by
  have hi : Integrable (fun z => (‖z‖^2+‖correspondenceLogPotential z‖)*‖θ z‖) volume := by
    have hn : LocallyIntegrable (fun z : ℂ => ‖z‖^2+‖correspondenceLogPotential z‖) volume :=
      ((continuous_norm.pow 2).locallyIntegrable).add
        (fun z => by
          obtain ⟨s, hs, hi⟩ := correspondenceLogPotential_locallyIntegrable z
          exact ⟨s, hs, hi.norm⟩)
    simpa only [smul_eq_mul] using hn.integrable_smul_right_of_hasCompactSupport
      hθ.norm (hc.comp_left norm_zero)
  have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
    exact ae_iff.mpr (by simp)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z => (‖z‖^2+‖correspondenceLogPotential z‖)*‖θ z‖)
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact ((Complex.continuous_ofReal.comp (correspondenceLogRegularized_contDiff τ
        hτ).continuous).mul hθ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, eventually_le_nhds (by norm_num : (0 : ℝ) < 1)
      |>.filter_mono nhdsWithin_le_nhds] with τ hτ hτ1
    filter_upwards [hne] with z hz
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (correspondenceLogRegularized_norm_le τ hτ hτ1 z hz)
        (norm_nonneg _)
  · exact hi
  · filter_upwards [hne] with z hz
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (correspondenceLogRegularized_tendsto z hz)).mul tendsto_const_nhds

end
end GinibrePoincare
