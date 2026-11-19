/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLaplaceBounds.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLaplaceOrbit

/-!
# Ginibre transition analytic Laplace bounds

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `actualNormalizedLaplaceIntegral_norm_bound`.
-/

@[expose] public section

open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

/-- The genuine positive normalized exponential weight has mass one. -/
theorem actualNormalizedLaplaceWeight_mass (c : ℝ) (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), c*Real.exp (-c*t))=1 := by
  rw [integral_const_mul]
  have h := integral_exp_mul_Ioi (show -c<0 by linarith) 0
  rw [h]
  simp only [mul_zero, Real.exp_zero]
  field_simp

theorem actualNormalizedLaplaceWeight_integrable (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => c*Real.exp (-c*t)) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (show -c<0 by linarith) 0).const_mul c

/-- A genuinely bounded measurable orbit has a bounded normalized Laplace
integral, with the exact same bound. -/
theorem actualNormalizedLaplaceIntegral_norm_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ → E) (c A : ℝ) (hc : 0 < c)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioi 0)))
    (hb : ∀ᵐ t ∂volume.restrict (Ioi 0), ‖a t‖ ≤ A) :
    IntegrableOn (fun t : ℝ => (c*Real.exp (-c*t)) • a t) (Ioi 0) ∧
      ‖∫ t in Ioi (0 : ℝ), (c*Real.exp (-c*t)) • a t‖≤A := by
  let w := fun t : ℝ => c*Real.exp (-c*t)
  have hw := actualNormalizedLaplaceWeight_integrable c hc
  have hmeas : AEStronglyMeasurable (fun t => w t • a t) (volume.restrict (Ioi 0)) :=
    hw.aestronglyMeasurable.smul ha
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi 0), ‖w t • a t‖≤A*w t := by
    filter_upwards [hb] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le (Real.exp_pos _).le)]
    exact (mul_le_mul_of_nonneg_left ht (mul_nonneg hc.le (Real.exp_pos _).le)).trans_eq (mul_comm _
        _)
  have hi := (hw.const_mul A).mono' hmeas hbound
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖w t • a t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), A*w t := integral_mono_ae hi.norm (hw.const_mul A) hbound
    _ = A := by rw [integral_const_mul, actualNormalizedLaplaceWeight_mass c hc, mul_one]

end
end GinibrePoincare
