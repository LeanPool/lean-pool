/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralConditional.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralLinear
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! Conditional centering in the actual null-augmented Brownian past. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_augmented_increment_condExp_zero {Ω ι : Type*}
    [mAmbient : MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) :
    P[(fun ω => B i (s+t) ω-B i s ω) | ginibreBrownianAugmentedFiltration B P hB s] =ᵐ[P]
      (fun _ => 0) := by
  have := Fintype.ofFinite ι
  let X := fun ω j => B j (s+t) ω-B j s ω
  have hXM : Measurable X := by
    apply Measurable.of_eval
    intro j
    exact (aemeasurable_iff_measurable.mp ((hB j).aemeasurable (s+t))).sub
      (aemeasurable_iff_measurable.mp ((hB j).aemeasurable s))
  have hi := indep_nullAugmentation_right P (MeasurableSpace.comap X inferInstance)
    (ginibreBrownianFamilyPastSpace B s) hXM.comap_le (ginibreBrownianFamilyPastSpace_le B P hB s)
    (ginibreBrownian_family_increment_independent_past B P hB hind s t)
  have hx : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (fun ω => B i (s+t) ω-B i s ω) :=
    ((measurable_pi_apply i).comp (comap_measurable X)).stronglyMeasurable
  have hh := condExp_indep_eq hXM.comap_le ((ginibreBrownianAugmentedFiltration B P hB).le s) hx hi
  have hZ : HasLaw (fun ω => B i (s+t) ω-B i s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hMean : (∫ ω, B i (s+t) ω-B i s ω ∂P) = 0 := by
    have h := hZ.integral_comp (show AEStronglyMeasurable (id : ℝ → ℝ) (gaussianReal 0 t) by
        fun_prop)
    simpa using h.trans (integral_id_gaussianReal (μ := 0) (v := t))
  simpa only [hMean] using hh

theorem ginibreBrownian_augmented_linear_condExp_zero {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hFi : MemLp F 2 P) :
    P[(fun ω => F ω*(B i (s+t) ω-B i s ω)) | ginibreBrownianAugmentedFiltration B P hB s] =ᵐ[P]
      (fun _ => 0) := by
  have := Fintype.ofFinite ι
  have hp := ginibreBrownian_augmented_linear_memLp_two B P hB hind s t i F hF hFi
  have hl : HasLaw (fun ω => B i (s+t) ω-B i s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hmap : Integrable id (P.map (fun ω => B i (s+t) ω-B i s ω)) := by
    rw [hl.map_eq]
    exact (IsGaussian.memLp_two_id).integrable (by norm_num)
  have hZ : Integrable (fun ω => B i (s+t) ω-B i s ω) P :=
    hmap.comp_aemeasurable hl.aemeasurable
  have hh := condExp_mul_of_stronglyMeasurable_left hF.stronglyMeasurable
    (hp.integrable (by norm_num)) hZ
  apply hh.trans
  filter_upwards [ginibreBrownian_augmented_increment_condExp_zero B P hB hind s t i] with ω hω
  simp only [Pi.mul_apply, hω, mul_zero]

end
end GinibrePoincare
