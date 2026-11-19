/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGirsanovVectorFiniteMoments.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovVectorFinite

/-!
# Brownian integral Girsanov vector finite moments

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianPredictableVectorGaussianDensity_lintegral_sq_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem brownianPredictableVectorGaussianDensity_lintegral_step_sq
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι → ℝ) (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (N : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ (N+1) ω)^2 ∂P)=
      ∫⁻ ω, ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω)^2*
        ENNReal.ofReal (Real.exp ((∑ i, (h N ω i)^2)*((τ (N+1)-τ N : ℝ≥0) : ℝ))) ∂P := by
  classical
  let Y := fun ω => (h N ω, brownianPredictableVectorGaussianDensity B h τ N ω)
  have hY : @Measurable Ω ((ι→ℝ)×ℝ) (ginibreBrownianAugmentedFiltration B P hB (τ N)) _ Y :=
    (hh N).prodMk (brownianPredictableVectorGaussianDensity_measurable_at B P hB h τ hτ hh N)
  have hYa := hY.mono ((ginibreBrownianAugmentedFiltration B P hB).le (τ N)) le_rfl
  let X := fun ω i => B i (τ (N+1)) ω-B i (τ N) ω
  have hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 (τ (N+1)-τ N))) P := by
    have hl := ginibreBrownian_family_increment_hasLaw B P hB hind (τ N) (τ (N+1)-τ N)
    simpa only [add_tsub_cancel_of_le (hτ (Nat.le_succ N))] using hl
  have hi : IndepFun Y X P := by
    have hi := (brownianFamily_fresh_increment_independent_augmented_variable B P hB hind
      (τ N) (τ (N+1)-τ N) Y hY).symm
    simpa only [add_tsub_cancel_of_le (hτ (Nat.le_succ N))] using hi
  have he := gaussianVectorPredictableTilt_lintegral_sq P Y X hYa.aemeasurable
    (τ (N+1)-τ N) hX hi Prod.fst (fun y : (ι→ℝ)×ℝ => ENNReal.ofReal y.2^2)
    measurable_fst ((ENNReal.measurable_ofReal.comp measurable_snd).pow_const 2)
  simp only [Y, X] at he
  simp_rw [brownianPredictableVectorGaussianDensity_succ,
    ENNReal.ofReal_mul (brownianPredictableVectorGaussianDensity_pos B h τ N _).le, mul_pow]
  exact he

/-- Genuine uniform second-moment bound for the finite predictable Gaussian
Radon--Nikodym densities of the original Brownian family. -/
theorem brownianPredictableVectorGaussianDensity_lintegral_sq_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (h0 : τ 0 = 0)
    (hh : ∀ k, @Measurable Ω (ι → ℝ) (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (C : ℝ) (_ : 0 ≤ C) (hb : ∀ k ω, (∑ i, (h k ω i) ^ 2) ≤ C ^ 2) (N : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω)^2 ∂P) ≤
      ENNReal.ofReal (Real.exp (C^2*(τ N : ℝ))) := by
  classical
  induction N with
  | zero => simp [brownianPredictableVectorGaussianDensity, h0]
  | succ N ih =>
    rw [brownianPredictableVectorGaussianDensity_lintegral_step_sq B P hB hind h τ hτ hh N]
    have he (ω : Ω) : ENNReal.ofReal (Real.exp ((∑ i, (h N ω i)^2)*((τ (N+1)-τ N : ℝ≥0) : ℝ))) ≤
        ENNReal.ofReal (Real.exp (C^2*((τ (N+1)-τ N : ℝ≥0) : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
      exact hb N ω
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω)^2*
          ENNReal.ofReal (Real.exp (C^2*((τ (N+1)-τ N : ℝ≥0) : ℝ))) ∂P :=
        lintegral_mono (fun ω => mul_le_mul' le_rfl (he ω))
      _ = (∫⁻ ω, ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω)^2 ∂P)*
          ENNReal.ofReal (Real.exp (C^2*((τ (N+1)-τ N : ℝ≥0) : ℝ))) := by
        rw [lintegral_mul_const _ (by
          have hm := (brownianPredictableVectorGaussianDensity_measurable_at B P hB h τ hτ hh
              N).mono
            ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl
          exact (ENNReal.measurable_ofReal.comp hm).pow_const 2)]
      _ ≤ ENNReal.ofReal (Real.exp (C^2*(τ N : ℝ)))*
          ENNReal.ofReal (Real.exp (C^2*((τ (N+1)-τ N : ℝ≥0) : ℝ))) := mul_le_mul' ih le_rfl
      _ = ENNReal.ofReal (Real.exp (C^2*(τ (N+1) : ℝ))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,
          NNReal.coe_sub (hτ (Nat.le_succ N))]
        congr 2
        ring

end
end GinibrePoincare
