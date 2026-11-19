/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticAugmentedMixedOrthogonality.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticAugmentedMixedMoments

/-! Genuine orthogonality of disjoint augmented predictable mixed-coordinate innovations. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_augmented_mixed_disjoint_orthogonal {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t r v : ℝ≥0) (hst : s + t ≤ r) (i j k l : ι) (hkl : k ≠ l) (F G : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hG : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ G) :
    (∫ ω, (F ω*((B i (s+t) ω-B i s ω)*(B j (s+t) ω-B j s ω)))*
      (G ω*((B k (r+v) ω-B k r ω)*(B l (r+v) ω-B l r ω))) ∂P) = 0 := by
  have := Fintype.ofFinite ι
  let H := fun ω => F ω*((B i (s+t) ω-B i s ω)*(B j (s+t) ω-B j s ω))*G ω
  have hsr : s ≤ r := (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le)).trans hst
  have hOld (a : ι) : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _
      (fun ω => B a (s+t) ω-B a s ω) :=
    (ginibreBrownian_augmented_coordinate_measurable_at B P hB r (s+t) hst a).sub
      (ginibreBrownian_augmented_coordinate_measurable_at B P hB r s hsr a)
  have hHM : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ H :=
    ((hF.mono ((ginibreBrownianAugmentedFiltration B P hB).mono hsr) le_rfl).mul
      ((hOld i).mul (hOld j))).mul hG
  have hH : Measurable H := hHM.mono ((ginibreBrownianAugmentedFiltration B P hB).le r) le_rfl
  have hFresh := brownianFamily_fresh_increment_independent_augmented_variable B P hB hind r v H hHM
  have hφ : Measurable (fun z : ι → ℝ => z k*z l) := (measurable_pi_apply k).mul
      (measurable_pi_apply l)
  have hInd := hFresh.comp hφ measurable_id
  have hLaw (a : ι) : HasLaw (fun ω => B a (r+v) ω-B a r ω) (gaussianReal 0 v) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B a) P (hB a) r (r+v)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ v from bot_le))
  have hp := hInd.symm.integral_mul_eq_mul_integral
    (by convert! hH.aestronglyMeasurable using 1)
    (by convert! ((hLaw k).aemeasurable.aestronglyMeasurable.mul (hLaw
          l).aemeasurable.aestronglyMeasurable) using 1)
  simp only [Function.comp_def, Pi.mul_apply, id_eq] at hp
  calc
    _ = ∫ ω, H ω*((B k (r+v) ω-B k r ω)*(B l (r+v) ω-B l r ω)) ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => by dsimp [H]; ring)
    _ = 0 := by rw [hp, ginibreBrownian_family_mixed_increment_mean B P hB hind r v k l hkl,
                  mul_zero]

end
end GinibrePoincare
