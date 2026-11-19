/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGirsanovTerminalFresh.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovPastMarginal

/-!
# Brownian integral Girsanov terminal fresh

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianPredictableVectorGaussianDensity_terminal_fresh_increment`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- Every chronological corrected block is fresh under the actual full
terminal likelihood, including independence from the entire original past. -/
theorem brownianPredictableVectorGaussianDensity_terminal_fresh_increment
    {Ω ι α : Type*} [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace α]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι → ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (k N : ℕ) (hkN : k < N) (Y : Ω → α)
    (hY : @Measurable Ω α (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ Y) :
    let Q := P.withDensity (fun ω => ENNReal.ofReal
      (brownianPredictableVectorGaussianDensity B h τ N ω))
    let W := fun ω i => B i (τ (k+1)) ω-B i (τ k) ω-
      h k ω i*((τ (k+1)-τ k : ℝ≥0) : ℝ)
    HasLaw W (Measure.pi (fun _ : ι => gaussianReal 0 (τ (k+1)-τ k))) Q ∧
      IndepFun Y W Q := by
  classical
  dsimp only
  let Q (K : ℕ) := P.withDensity (fun ω => ENNReal.ofReal
    (brownianPredictableVectorGaussianDensity B h τ K ω))
  let W := fun ω i => B i (τ (k+1)) ω-B i (τ k) ω-
      h k ω i*((τ (k+1)-τ k : ℝ≥0) : ℝ)
  let (K : ℕ) : IsProbabilityMeasure (Q K) :=
    brownianPredictableVectorGaussianDensity_isProbabilityMeasure B P hB hind h τ hτ hh K
  have hW : @Measurable Ω (ι→ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ (k+1))) _ W := by
    refine (@measurable_pi_iff Ω ι (fun _ => ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ (k+1))) (fun _ => inferInstance) W).mpr ?_
    intro i
    exact ((ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ (k+1)) _ le_rfl i).sub
      (ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ (k+1)) _
        (hτ (Nat.le_succ k)) i)).sub
      (((measurable_pi_apply i).comp ((hh k).mono
        ((ginibreBrownianAugmentedFiltration B P hB).mono (hτ (Nat.le_succ k))) le_rfl)).mul_const
            _)
  have hYnext := hY.mono
    ((ginibreBrownianAugmentedFiltration B P hB).mono (hτ (Nat.le_succ k))) le_rfl
  have hYa := hY.mono ((ginibreBrownianAugmentedFiltration B P hB).le (τ k)) le_rfl
  have hWa := hW.mono ((ginibreBrownianAugmentedFiltration B P hB).le (τ (k+1))) le_rfl
  have hmapY : (Q N).map Y=(Q (k+1)).map Y :=
    brownianPredictableVectorGaussianDensity_past_map B P hB hind h τ hτ hh
      (k+1) N (Nat.succ_le_of_lt hkN) Y hYnext
  have hmapW : (Q N).map W=(Q (k+1)).map W :=
    brownianPredictableVectorGaussianDensity_past_map B P hB hind h τ hτ hh
      (k+1) N (Nat.succ_le_of_lt hkN) W hW
  have hmapPair : (Q N).map (fun ω => (Y ω, W ω))=
      (Q (k+1)).map (fun ω => (Y ω, W ω)) :=
    brownianPredictableVectorGaussianDensity_past_map B P hB hind h τ hτ hh
      (k+1) N (Nat.succ_le_of_lt hkN) _ (hYnext.prodMk hW)
  have hf := brownianPredictableVectorGaussianDensity_fresh_increment B P hB hind h τ hτ hh k Y hY
  dsimp only at hf
  refine ⟨⟨hWa.aemeasurable, hmapW.trans hf.1.map_eq⟩,?_⟩
  apply (indepFun_iff_map_prod_eq_prod_map_map hYa.aemeasurable hWa.aemeasurable).mpr
  rw [hmapPair, hmapY, hmapW]
  exact hf.2.map_prod_eq_prod_map_map hYa.aemeasurable hWa.aemeasurable

end
end GinibrePoincare
