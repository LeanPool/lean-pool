/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticAugmentedMixedMoments.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticAugmentedQuadraticOrthogonality

/-! Actual mixed-coordinate Brownian innovations and predictable square moments. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_family_distinct_increment_independent {Ω ι : Type*} [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i j : ι) (hij : i ≠ j) :
    IndepFun (fun ω => B i (s+t) ω-B i s ω) (fun ω => B j (s+t) ω-B j s ω) P := by
  exact (hind.indepFun hij).comp ((measurable_pi_apply (s+t)).sub (measurable_pi_apply s))
    ((measurable_pi_apply (s+t)).sub (measurable_pi_apply s))

theorem ginibreBrownian_family_mixed_increment_mean {Ω ι : Type*} [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i j : ι) (hij : i ≠ j) :
    (∫ ω, (B i (s+t) ω-B i s ω)*(B j (s+t) ω-B j s ω) ∂P) = 0 := by
  have hLaw (k : ι) : HasLaw (fun ω => B k (s+t) ω-B k s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B k) P (hB k) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hp := (ginibreBrownian_family_distinct_increment_independent B P hind s t i j
      hij).integral_mul_eq_mul_integral
    (hLaw i).aemeasurable.aestronglyMeasurable (hLaw j).aemeasurable.aestronglyMeasurable
  simp only [Pi.mul_apply] at hp
  have hm := (hLaw i).integral_comp (show AEStronglyMeasurable id (gaussianReal 0 t) by fun_prop)
  simp only [Function.comp_def, id_eq, integral_id_gaussianReal] at hm
  rw [hp, hm, zero_mul]

theorem ginibreBrownian_family_mixed_increment_secondMoment {Ω ι : Type*} [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i j : ι) (hij : i ≠ j) :
    (∫ ω, ((B i (s+t) ω-B i s ω)*(B j (s+t) ω-B j s ω))^2 ∂P) = (t : ℝ)^2 := by
  have hLaw (k : ι) : HasLaw (fun ω => B k (s+t) ω-B k s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B k) P (hB k) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hp := ((ginibreBrownian_family_distinct_increment_independent B P hind s t i j hij).comp
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integral_mul_eq_mul_integral
    (by convert! (hLaw i).aemeasurable.aestronglyMeasurable.pow 2 using 1)
    (by convert! (hLaw j).aemeasurable.aestronglyMeasurable.pow 2 using 1)
  simp only [Pi.mul_apply, Function.comp_apply, id_eq] at hp
  simp_rw [mul_pow]
  rw [hp, ginibreGaussian_hasLaw_square_mean P _ t (hLaw i), ginibreGaussian_hasLaw_square_mean P _
      t (hLaw j), pow_two]

theorem ginibreBrownian_augmented_mixed_secondMoment {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i j : ι) (hij : i ≠ j) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F) :
    (∫ ω, (F ω*((B i (s+t) ω-B i s ω)*(B j (s+t) ω-B j s ω)))^2 ∂P) =
      (t : ℝ)^2*(∫ ω, (F ω)^2 ∂P) := by
  have := Fintype.ofFinite ι
  have hFresh := brownianFamily_fresh_increment_independent_augmented_variable B P hB hind s t F hF
  have hφ : Measurable (fun z : ι → ℝ => z i*z j) := (measurable_pi_apply i).mul
      (measurable_pi_apply j)
  have hInd := hFresh.comp hφ measurable_id
  have hFM : Measurable F := hF.mono ((ginibreBrownianAugmentedFiltration B P hB).le s) le_rfl
  have hZ : Measurable (fun ω => (B i (s+t) ω-B i s ω)*(B j (s+t) ω-B j s ω)) :=
    ((aemeasurable_iff_measurable.mp ((hB i).aemeasurable (s+t))).sub
      (aemeasurable_iff_measurable.mp ((hB i).aemeasurable s))).mul
      ((aemeasurable_iff_measurable.mp ((hB j).aemeasurable (s+t))).sub
        (aemeasurable_iff_measurable.mp ((hB j).aemeasurable s)))
  have hp := (hInd.symm.comp (measurable_id.pow_const 2) (measurable_id.pow_const
      2)).integral_mul_eq_mul_integral
    (hFM.pow_const 2).aestronglyMeasurable (hZ.pow_const 2).aestronglyMeasurable
  simp only [Pi.mul_apply, Function.comp_apply, id_eq] at hp
  calc
    _ = ∫ ω, (F ω)^2*((B i (s+t) ω-B i s ω)*(B j (s+t) ω-B j s ω))^2 ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => by ring)
    _ = _ := by
      rw [hp, ginibreBrownian_family_mixed_increment_secondMoment B P hB hind s t i j hij]
      ring

theorem ginibreBrownian_family_mixed_increment_memLp_two {Ω ι : Type*} [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i j : ι) (hij : i ≠ j) :
    MemLp (fun ω => (B i (s+t) ω-B i s ω)*(B j (s+t) ω-B j s ω)) 2 P := by
  have hLaw (k : ι) : HasLaw (fun ω => B k (s+t) ω-B k s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B k) P (hB k) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hSq (k : ι) := ginibreGaussian_hasLaw_square_memLp_two P _ t (hLaw k)
  apply (memLp_two_iff_integrable_sq ((hLaw i).aemeasurable.aestronglyMeasurable.mul
    (hLaw j).aemeasurable.aestronglyMeasurable)).mpr
  change Integrable (fun ω => ((B i (s+t) ω-B i s ω)*(B j (s+t) ω-B j s ω))^2) P
  simp_rw [mul_pow]
  have h := ((ginibreBrownian_family_distinct_increment_independent B P hind s t i j hij).comp
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
    (by convert! (hSq i).integrable (by norm_num) using 1)
    (by convert! (hSq j).integrable (by norm_num) using 1)
  convert! h using 1

theorem ginibreBrownian_augmented_mixed_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i j : ι) (hij : i ≠ j) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hFi : MemLp F 2 P) :
    MemLp (fun ω => F ω*((B i (s+t) ω-B i s ω)*(B j (s+t) ω-B j s ω))) 2 P := by
  have := Fintype.ofFinite ι
  have hCross := ginibreBrownian_family_mixed_increment_memLp_two B P hB hind s t i j hij
  have hFresh := brownianFamily_fresh_increment_independent_augmented_variable B P hB hind s t F hF
  have hφ : Measurable (fun z : ι → ℝ => z i*z j) := (measurable_pi_apply i).mul
      (measurable_pi_apply j)
  have hInd := hFresh.comp hφ measurable_id
  apply (memLp_two_iff_integrable_sq (hFi.aestronglyMeasurable.mul hCross.aestronglyMeasurable)).mpr
  have h := (hInd.symm.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
    (by convert! hFi.integrable_sq using 1) (by convert! hCross.integrable_sq using 1)
  simp only [Function.comp_def, id_eq] at h
  convert! h using 1
  ext ω
  dsimp only [Pi.mul_apply, Pi.pow_apply]
  ring

end
end GinibrePoincare
