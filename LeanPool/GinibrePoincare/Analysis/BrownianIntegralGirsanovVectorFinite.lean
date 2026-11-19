/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGirsanovVectorFinite.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianTiltVectorPredictable
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralBaseMartingale

/-!
# Brownian integral Girsanov vector finite

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianPredictableVectorGaussianDensity_lintegral`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The discrete Girsanov density for the predictable drift `h` on the grid `τ`:
`exp (∑ k < N, ∑ i, (h k i * ΔB i k - (h k i) ^ 2 * Δτ k / 2))`. -/
def brownianPredictableVectorGaussianDensity {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) : ℝ :=
  Real.exp (∑ k ∈ Finset.range N, ∑ i,
    (h k ω i*(B i (τ (k+1)) ω-B i (τ k) ω)-(h k ω i)^2*((τ (k+1)-τ k : ℝ≥0) : ℝ)/2))

theorem brownianPredictableVectorGaussianDensity_pos {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) :
    0<brownianPredictableVectorGaussianDensity B h τ N ω := Real.exp_pos _

theorem brownianPredictableVectorGaussianDensity_succ {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) :
    brownianPredictableVectorGaussianDensity B h τ (N+1) ω =
      brownianPredictableVectorGaussianDensity B h τ N ω*
        gaussianVectorExponentialTilt (h N ω) (τ (N+1)-τ N)
          (fun i => B i (τ (N+1)) ω-B i (τ N) ω) := by
  classical
  simp only [brownianPredictableVectorGaussianDensity, Finset.sum_range_succ, Real.exp_add,
    gaussianVectorExponentialTilt_eq_exp]

theorem brownianPredictableVectorGaussianDensity_measurable_at
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι → ℝ) (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (N : ℕ) : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (τ N)) _
      (brownianPredictableVectorGaussianDensity B h τ N) := by
  classical
  have hmterm (k : ℕ) (hk : k<N) (i : ι) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P hB (τ N)) _ (fun ω =>
        h k ω i*(B i (τ (k+1)) ω-B i (τ k) ω)-(h k ω i)^2*((τ (k+1)-τ k : ℝ≥0) : ℝ)/2) := by
    have hmH := (measurable_pi_apply i).comp
      ((hh k).mono ((ginibreBrownianAugmentedFiltration B P hB).mono (hτ hk.le)) le_rfl)
    have hmX := (ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ N) _
      (hτ (Nat.succ_le_of_lt hk)) i).sub
      (ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ N) _ (hτ hk.le) i)
    have hm := (hmH.mul hmX).sub (((hmH.pow_const 2).mul_const (((τ (k+1)-τ k : ℝ≥0) :
        ℝ))).div_const 2)
    exact hm
  let : MeasurableSpace Ω := ginibreBrownianAugmentedFiltration B P hB (τ N)
  unfold brownianPredictableVectorGaussianDensity
  apply Measurable.exp
  apply Finset.measurable_sum
  intro k hk
  apply Finset.measurable_sum
  intro i hi
  exact hmterm k (Finset.mem_range.mp hk) i

/-- Genuine normalization for an arbitrary predictable vector field against
all independent original Brownian coordinates simultaneously. -/
theorem brownianPredictableVectorGaussianDensity_lintegral
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι → ℝ) (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (N : ℕ) : (∫⁻ ω, ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω) ∂P)=1 := by
  classical
  induction N with
  | zero => simp [brownianPredictableVectorGaussianDensity]
  | succ N ih =>
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
    have he := gaussianVectorPredictableTilt_lintegral P Y X hYa.aemeasurable
      (τ (N+1)-τ N) hX hi Prod.fst (fun y : (ι→ℝ)×ℝ => ENNReal.ofReal y.2)
      measurable_fst (ENNReal.measurable_ofReal.comp measurable_snd)
    simp only [Y, X] at he
    simp_rw [brownianPredictableVectorGaussianDensity_succ,
      ENNReal.ofReal_mul (brownianPredictableVectorGaussianDensity_pos B h τ N _).le]
    exact he.trans ih

end
end GinibrePoincare
