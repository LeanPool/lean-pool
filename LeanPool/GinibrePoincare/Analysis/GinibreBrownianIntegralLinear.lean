/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralLinear.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOrthogonalSquareSum

/-! Linear Brownian innovations with coefficients measurable in the genuine augmented past. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_augmented_linear_secondMoment {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F) :
    (∫ ω, (F ω*(B i (s+t) ω-B i s ω))^2 ∂P) =
      (t : ℝ)*(∫ ω, (F ω)^2 ∂P) := by
  have := Fintype.ofFinite ι
  have hZ : HasLaw (fun ω => B i (s+t) ω-B i s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hFM : Measurable F := hF.mono ((ginibreBrownianAugmentedFiltration B P hB).le s) le_rfl
  have hInd := ginibreBrownian_augmented_coordinate_increment_independent B P hB hind s t i F hF
  have hp := (hInd.symm.comp (measurable_id.pow_const 2) (show Measurable (fun z : ℝ => z^2) by
      fun_prop)).integral_mul_eq_mul_integral
    (hFM.pow_const 2).aestronglyMeasurable (hZ.aemeasurable.aestronglyMeasurable.pow 2)
  simp only [Pi.mul_apply, Function.comp_apply, id_eq] at hp
  simp_rw [mul_pow]
  rw [hp, ginibreGaussian_hasLaw_square_mean P _ t hZ, mul_comm]

theorem ginibreBrownian_augmented_linear_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hFi : MemLp F 2 P) :
    MemLp (fun ω => F ω*(B i (s+t) ω-B i s ω)) 2 P := by
  have := Fintype.ofFinite ι
  have hZ : HasLaw (fun ω => B i (s+t) ω-B i s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hFM : Measurable F := hF.mono ((ginibreBrownianAugmentedFiltration B P hB).le s) le_rfl
  have hInd := ginibreBrownian_augmented_coordinate_increment_independent B P hB hind s t i F hF
  exact ginibreIndependent_predictable_memLp_two P F _ hFM _ hZ hInd id measurable_id hFi
    id measurable_id (IsGaussian.memLp_two_id)

theorem ginibreBrownian_augmented_linear_disjoint_orthogonal {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t r v : ℝ≥0) (hst : s + t ≤ r) (i j : ι) (F G : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hG : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ G) :
    (∫ ω, (F ω*(B i (s+t) ω-B i s ω))*(G ω*(B j (r+v) ω-B j r ω)) ∂P) = 0 := by
  have := Fintype.ofFinite ι
  let H := fun ω => F ω*(B i (s+t) ω-B i s ω)*G ω
  have hsr : s ≤ r := (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le)).trans hst
  have hHM : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ H :=
    ((hF.mono ((ginibreBrownianAugmentedFiltration B P hB).mono hsr) le_rfl).mul
      ((ginibreBrownian_augmented_coordinate_measurable_at B P hB r (s+t) hst i).sub
        (ginibreBrownian_augmented_coordinate_measurable_at B P hB r s hsr i))).mul hG
  have hH : Measurable H := hHM.mono ((ginibreBrownianAugmentedFiltration B P hB).le r) le_rfl
  have hZ : HasLaw (fun ω => B j (r+v) ω-B j r ω) (gaussianReal 0 v) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B j) P (hB j) r (r+v)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ v from bot_le))
  have hMean : (∫ ω, B j (r+v) ω-B j r ω ∂P) = 0 := by
    have hh := hZ.integral_comp (show AEStronglyMeasurable (id : ℝ → ℝ) (gaussianReal 0 v) by
        fun_prop)
    simpa using hh.trans (integral_id_gaussianReal (μ := 0) (v := v))
  have hInd := ginibreBrownian_augmented_coordinate_increment_independent B P hB hind r v j H hHM
  have hp := hInd.symm.integral_mul_eq_mul_integral hH.aestronglyMeasurable
      hZ.aemeasurable.aestronglyMeasurable
  simp only [Pi.mul_apply] at hp
  calc
    _ = ∫ ω, H ω*(B j (r+v) ω-B j r ω) ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => by dsimp [H]; ring)
    _ = 0 := by rw [hp, hMean, mul_zero]

end
end GinibrePoincare
