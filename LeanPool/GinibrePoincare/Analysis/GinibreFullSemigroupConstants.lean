/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare.

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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorResolvent
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare

/-! # Constants and conservation for the full weak resolvent -/

@[expose] public section

open MeasureTheory Filter
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section

/-- The concrete Riesz resolvent fixes every actual real constant. -/
theorem ginibreFullValueResolvent_constant (n : ℕ) (hn : 0 < n) (c : ℝ) :
    ginibreFullValueResolvent n hn (ginibreRealConstantL2 n hn c) =
      ginibreRealConstantL2 n hn c := by
  have he := ginibreFullGenerator_resolvent_unique n hn
    (ginibreRealConstantL2 n hn c) (ginibreRealConstantL2 n hn c) 0
    (ginibreRealConstantL2_weak n hn c) (ginibreRealConstantL2_symmetric_pair n hn c)
    (by intro v h hv hs; simp)
  exact he.1.symm

/-- The full real weak resolvent preserves the equilibrium integral. -/
theorem ginibreFullValueResolvent_mean (n : ℕ) (hn : 0 < n) (u : GinibreFullValueL2 n) :
    ginibreL2Mean n (ginibreFullValueResolvent n hn u) = ginibreL2Mean n u := by
  rw [← ginibreRealConstantL2_one_inner n hn, ← ginibreRealConstantL2_one_inner n hn]
  rw [← ginibreFullValueResolvent_symmetric, ginibreFullValueResolvent_constant]

/-- The sharp gap gives the concrete full real resolvent contraction `1/3`
 on every zero-mean datum. -/
theorem ginibreFullValueResolvent_centered_norm_le (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) (hf : ginibreL2Mean n f = 0) :
    ‖ginibreFullValueResolvent n hn f‖ ≤ ‖f‖ / 3 := by
  let p := ginibreFullFormResolvent n hn f
  let u := ginibreFullFormValue n hn p
  let g := ginibreFullFormGradient n hn p
  have hm : ginibreL2Mean n u = 0 := (ginibreFullValueResolvent_mean n hn f).trans hf
  have hp := ginibre_symmetric_weak_poincare hn u g
    (ginibreFullFormSpace_weak n hn p).1 (ginibreFullFormSpace_weak n hn p).2
  have hv : ginibreL2Variance n hn u = ‖u‖ ^ 2 := by
    simp only [ginibreL2Variance, hm, ginibreRealConstantL2_zero, sub_zero]
  rw [hv] at hp
  have he := ginibreFullFormSpace_inner n hn p p
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at he
  have hr := ginibreFullFormResolvent_riesz n hn f p
  rw [real_inner_self_eq_norm_sq] at hr
  have hc := real_inner_le_norm f u
  have hmain : 3 * ‖u‖ ^ 2 ≤ ‖f‖ * ‖u‖ := by
    change ‖p‖ ^ 2 = ‖u‖ ^ 2 + (1 / (n : ℝ)) * ‖g‖ ^ 2 at he
    change ‖p‖ ^ 2 = inner ℝ f u at hr
    change ‖u‖ ^ 2 ≤ ((1 / (n : ℝ)) * ‖g‖ ^ 2) / 2 at hp
    nlinarith
  change ‖u‖ ≤ ‖f‖ / 3
  by_cases hu : ‖u‖ = 0
  · rw [hu]; positivity
  · have hpos := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
    nlinarith

/-- Exact real resolvent fixed-space: the equilibrium constants. -/
theorem ginibreFullValueResolvent_fixed_iff_constant (n : ℕ) (hn : 0 < n)
    (u : GinibreFullValueL2 n) :
    ginibreFullValueResolvent n hn u = u ↔ u = ginibreRealConstantL2 n hn (ginibreL2Mean n u) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  constructor
  · intro hu
    let v := ginibreFullCenter n hn u
    have hv : ginibreL2Mean n v = 0 := by
      change ginibreL2Mean n (ginibreFullCenter n hn u) = 0
      rw [ginibreFullCenter_apply]
      change (∫ z, (u - ginibreRealConstantL2 n hn (ginibreL2Mean n u)) z ∂ginibreMeasure n) = 0
      have he : ((u - ginibreRealConstantL2 n hn (ginibreL2Mean n u) : GinibreFullValueL2 n) :
        Configuration n → ℝ) =ᵐ[ginibreMeasure n]
          fun z => u z - ginibreL2Mean n u := by
        filter_upwards [Lp.coeFn_sub u (ginibreRealConstantL2 n hn (ginibreL2Mean n u)),
          ginibreRealConstantL2_ae n hn (ginibreL2Mean n u)] with z hs hc
        rw [hs]
        change u z - (ginibreRealConstantL2 n hn (ginibreL2Mean n u)) z = _
        rw [hc]
      rw [integral_congr_ae he, integral_sub]
      · let := ginibreMeasure_isProbabilityMeasure hn
        simp [ginibreL2Mean]
      · exact (Lp.memLp u).integrable (by norm_num)
      · let := ginibreMeasure_isProbabilityMeasure hn
        exact integrable_const _
    have hRv : ginibreFullValueResolvent n hn v = v := by
      simp only [v, ginibreFullCenter_apply, map_sub, hu, ginibreFullValueResolvent_constant]
    have hnV := ginibreFullValueResolvent_centered_norm_le n hn v hv
    rw [hRv] at hnV
    have hz : v = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v])
    change ginibreFullCenter n hn u = 0 at hz
    rw [ginibreFullCenter_apply] at hz
    exact sub_eq_zero.mp hz
  · intro hu
    rw [hu, ginibreFullValueResolvent_constant]

end
end GinibrePoincare
