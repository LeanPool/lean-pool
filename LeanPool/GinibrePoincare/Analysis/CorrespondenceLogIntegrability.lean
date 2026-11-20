/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceLogIntegrability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceLogApproximation
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Correspondence log integrability

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `correspondenceLogPotential_locallyIntegrable`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory

/-- The logarithmic potential `z ↦ Real.log ‖z‖`. -/
def correspondenceLogPotential (z : ℂ) : ℝ := Real.log ‖z‖

theorem correspondenceLogPotential_locallyIntegrable :
    LocallyIntegrable correspondenceLogPotential volume := by
  have hi : LocallyIntegrable (fun z : ℂ => ‖z‖⁻¹) volume := by
    apply locallyIntegrable_of_norm_le_rpow (E := ℂ) (C := (1 : ℝ)) (α := (1 : ℝ))
    · norm_num [Complex.finrank_real_complex]
    · exact ae_of_all _ (fun z => by
        simp [
          Real.rpow_neg_one])
    · fun_prop
    · norm_num [Complex.finrank_real_complex]
  have hd := continuous_norm.locallyIntegrable.add hi
  apply hd.mono ((Real.measurable_log.comp continuous_norm.measurable).aestronglyMeasurable)
  apply ae_of_all
  intro z
  change ‖Real.log ‖z‖‖ ≤ ‖‖z‖+‖z‖⁻¹‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _)))]
  by_cases hz : z = 0
  · simp [hz]
  · have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have h1 := Real.log_le_sub_one_of_pos hr
    have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
    rw [Real.log_inv] at h2
    exact abs_le.mpr ⟨by linarith, by linarith [inv_nonneg.mpr hr.le]⟩

end
end GinibrePoincare

