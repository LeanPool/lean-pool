/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGirsanovFreshIncrement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianTiltFreshLaw

/-!
# Brownian integral Girsanov fresh increment

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianPredictableVectorGaussianDensity_fresh_increment`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- Under the genuine one-step chronological density, the drift-corrected
original Brownian family increment is Gaussian and independent of every
variable measurable in the original augmented past. -/
theorem brownianPredictableVectorGaussianDensity_fresh_increment
    {Ω ι α : Type*} [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace α]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι → ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (N : ℕ) (Y : Ω → α)
    (hY : @Measurable Ω α (ginibreBrownianAugmentedFiltration B P hB (τ N)) _ Y) :
    let Q := P.withDensity (fun ω => ENNReal.ofReal
      (brownianPredictableVectorGaussianDensity B h τ (N+1) ω))
    let W := fun ω i => B i (τ (N+1)) ω-B i (τ N) ω-
      h N ω i*((τ (N+1)-τ N : ℝ≥0) : ℝ)
    HasLaw W (Measure.pi (fun _ : ι => gaussianReal 0 (τ (N+1)-τ N))) Q ∧
      IndepFun Y W Q := by
  classical
  dsimp only
  let S := fun ω => (h N ω, (brownianPredictableVectorGaussianDensity B h τ N ω, Y ω))
  have hS : @Measurable Ω ((ι→ℝ)×(ℝ×α))
      (ginibreBrownianAugmentedFiltration B P hB (τ N)) _ S :=
    (hh N).prodMk ((brownianPredictableVectorGaussianDensity_measurable_at
      B P hB h τ hτ hh N).prodMk hY)
  have hSa := hS.mono ((ginibreBrownianAugmentedFiltration B P hB).le (τ N)) le_rfl
  let X := fun ω i => B i (τ (N+1)) ω-B i (τ N) ω
  have hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 (τ (N+1)-τ N))) P := by
    have hl := ginibreBrownian_family_increment_hasLaw B P hB hind (τ N) (τ (N+1)-τ N)
    simpa only [add_tsub_cancel_of_le (hτ (Nat.le_succ N))] using hl
  have hXm : Measurable X := by
    apply Measurable.of_eval
    intro i
    exact ((ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ (N+1)) _ le_rfl i).sub
      (ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ (N+1)) _
        (hτ (Nat.le_succ N)) i)).mono
      ((ginibreBrownianAugmentedFiltration B P hB).le (τ (N+1))) le_rfl
  have hi : IndepFun S X P := by
    have hi := (brownianFamily_fresh_increment_independent_augmented_variable B P hB hind
      (τ N) (τ (N+1)-τ N) S hS).symm
    simpa only [add_tsub_cancel_of_le (hτ (Nat.le_succ N))] using hi
  have he := gaussianVectorPredictableTilt_centered_fresh P S X hSa hXm
    (τ (N+1)-τ N) hX hi Prod.fst
    (fun s : (ι→ℝ)×(ℝ×α) => ENNReal.ofReal s.2.1)
    measurable_fst (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd))
    (brownianPredictableVectorGaussianDensity_lintegral B P hB hind h τ hτ hh N)
  dsimp only at he
  have hQ : P.withDensity (fun ω => ENNReal.ofReal
      (brownianPredictableVectorGaussianDensity B h τ (N+1) ω)) =
    P.withDensity (fun ω => ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω)*
      ENNReal.ofReal (gaussianVectorExponentialTilt (h N ω) (τ (N+1)-τ N) (X ω))) := by
    congr 1
    funext ω
    rw [brownianPredictableVectorGaussianDensity_succ,
      ENNReal.ofReal_mul (brownianPredictableVectorGaussianDensity_pos B h τ N ω).le]
  rw [hQ]
  refine ⟨he.2.1, ?_⟩
  exact he.2.2.comp (measurable_snd.comp measurable_snd) measurable_id

end
end GinibrePoincare
