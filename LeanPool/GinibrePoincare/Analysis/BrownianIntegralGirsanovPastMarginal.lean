/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGirsanovPastMarginal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovFreshIncrement

/-!
# Brownian integral Girsanov past marginal

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianPredictableVectorGaussianDensity_past_map`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- Future genuine Gaussian likelihood factors preserve every nonnegative
past test, with no boundedness or integrability hypothesis on the test. -/
theorem brownianPredictableVectorGaussianDensity_past_lintegral
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι → ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (m N : ℕ) (hmN : m ≤ N) (Z : Ω → ℝ≥0∞)
    (hZ : @Measurable Ω ℝ≥0∞ (ginibreBrownianAugmentedFiltration B P hB (τ m)) _ Z) :
    (∫⁻ ω, ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω)*Z ω ∂P)=
      ∫⁻ ω, ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ m ω)*Z ω ∂P := by
  classical
  induction N, hmN using Nat.le_induction with
  | base => rfl
  | succ N hmN ih =>
    let S := fun ω => (h N ω, (brownianPredictableVectorGaussianDensity B h τ N ω, Z ω))
    have hZN := hZ.mono ((ginibreBrownianAugmentedFiltration B P hB).mono (hτ hmN)) le_rfl
    have hS : @Measurable Ω ((ι→ℝ)×(ℝ×ℝ≥0∞))
        (ginibreBrownianAugmentedFiltration B P hB (τ N)) _ S :=
      (hh N).prodMk ((brownianPredictableVectorGaussianDensity_measurable_at
        B P hB h τ hτ hh N).prodMk hZN)
    have hSa := hS.mono ((ginibreBrownianAugmentedFiltration B P hB).le (τ N)) le_rfl
    let X := fun ω i => B i (τ (N+1)) ω-B i (τ N) ω
    have hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 (τ (N+1)-τ N))) P := by
      have hl := ginibreBrownian_family_increment_hasLaw B P hB hind (τ N) (τ (N+1)-τ N)
      simpa only [add_tsub_cancel_of_le (hτ (Nat.le_succ N))] using hl
    have hi : IndepFun S X P := by
      have hi := (brownianFamily_fresh_increment_independent_augmented_variable B P hB hind
        (τ N) (τ (N+1)-τ N) S hS).symm
      simpa only [add_tsub_cancel_of_le (hτ (Nat.le_succ N))] using hi
    have he := gaussianVectorPredictableTilt_lintegral P S X hSa.aemeasurable
      (τ (N+1)-τ N) hX hi Prod.fst
      (fun s : (ι→ℝ)×(ℝ×ℝ≥0∞) => ENNReal.ofReal s.2.1*s.2.2)
      measurable_fst ((ENNReal.measurable_ofReal.comp
        (measurable_fst.comp measurable_snd)).mul (measurable_snd.comp measurable_snd))
    simp only [S, X] at he
    simp_rw [brownianPredictableVectorGaussianDensity_succ,
      ENNReal.ofReal_mul (brownianPredictableVectorGaussianDensity_pos B h τ N _).le]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using he.trans ih

/-- The terminal likelihood has exactly the same past pushforward as the
likelihood stopped at that past time. -/
theorem brownianPredictableVectorGaussianDensity_past_map
    {Ω ι α : Type*} [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace α]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι → ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (m N : ℕ) (hmN : m ≤ N) (Y : Ω → α)
    (hY : @Measurable Ω α (ginibreBrownianAugmentedFiltration B P hB (τ m)) _ Y) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (brownianPredictableVectorGaussianDensity B h τ N ω))).map Y =
    (P.withDensity (fun ω => ENNReal.ofReal
      (brownianPredictableVectorGaussianDensity B h τ m ω))).map Y := by
  classical
  have hYa := hY.mono ((ginibreBrownianAugmentedFiltration B P hB).le (τ m)) le_rfl
  ext s hs
  rw [Measure.map_apply hYa hs, Measure.map_apply hYa hs,
    withDensity_apply _ (hYa hs), withDensity_apply _ (hYa hs)]
  have he := brownianPredictableVectorGaussianDensity_past_lintegral B P hB hind h τ hτ hh
    m N hmN ((Y ⁻¹' s).indicator (fun _ => 1)) (measurable_const.indicator (hY hs))
  have hp (K : ℕ) : (fun ω => ENNReal.ofReal
      (brownianPredictableVectorGaussianDensity B h τ K ω)*
      (Y ⁻¹' s).indicator (fun _ => 1) ω) =
    (Y ⁻¹' s).indicator (fun ω => ENNReal.ofReal
      (brownianPredictableVectorGaussianDensity B h τ K ω)) := by
    funext ω
    by_cases hw : Y ω∈s <;> simp [Set.indicator, hw]
  rw [hp N, hp m, lintegral_indicator (hYa hs), lintegral_indicator (hYa hs)] at he
  exact he

end
end GinibrePoincare
