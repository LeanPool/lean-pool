/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroLampertiIncrementShift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroLampertiIncrementIto
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianPuncturedShiftedLimit

/-! Actual shifted uniform sums of compact regularized Itô gradients converge
to increments of their genuine original martingale. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The real-coordinate vector of scaled derivatives `√(2α/n²) * ∂ᵢ f (X t ω)` of `f` along the
process `X`. -/
def ginibreConfigurationBrownianGradientField {Ω : Type*} (n : ℕ) (α : ℝ)
    (X : ℝ≥0 → Ω → Configuration n) (f : Configuration n → ℝ)
    (t : ℝ≥0) (ω : Ω) : EuclideanSpace ℝ (Fin n × Fin 2) :=
  WithLp.toLp 2 (fun i => Real.sqrt (2*α/(n : ℝ)^2)*
    fderiv ℝ f (X t ω) (ginibreCoordinateDirection i))

theorem ginibreConfigurationBrownianGradientField_sum_eq {Ω : Type*} (n : ℕ) (α : ℝ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (X : ℝ≥0 → Ω → Configuration n) (f : Configuration n → ℝ) (t : ℝ≥0) (k : ℕ) (ω : Ω) :
    (∑ i, brownianUniformLeftSum (B i)
      (fun u ω => ginibreConfigurationBrownianGradientField n α X f u ω i) t (k+1) ω) =
      ginibreConfigurationBrownianGradientSum n B α X f t k ω := by
  rw [ginibreConfigurationBrownianGradientSum_eq]
  simp only [ginibreConfigurationBrownianGradientField, PiLp.toLp_apply, brownianUniformLeftSum]
  simp_rw [mul_assoc,← Finset.mul_sum]

theorem ginibreCompactGradient_shifted_probability_limit
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (α : ℝ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (X : ℝ≥0 → Ω → Configuration n)
    (hX : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (T : ℝ≥0) (J : ℝ≥0 → Ω → ℝ)
    (hJ : ∀ t ≤ T, TendstoInMeasure P (ginibreConfigurationBrownianGradientSum n B α X f t) atTop (J
        t))
    (a r : ℝ≥0) (har : a + r ≤ T) :
    TendstoInMeasure P (fun k => brownianUnitShiftedUniformSum B
      (ginibreConfigurationBrownianGradientField n α X f) a r (k+1)) atTop
      (fun ω => J (a+r) ω-J a ω) := by
  obtain ⟨C, hC, hG, hH⟩ := ginibreCompactProcess_test_coefficients n _ X hX hCont f U K hU hf hK
      hKU hRange
  let d := Real.sqrt (2*α/(n : ℝ)^2)
  let u := ginibreConfigurationBrownianGradientField n α X f
  have hum (t : ℝ≥0) : @Measurable Ω (EuclideanSpace ℝ (Fin n × Fin 2))
      (ginibreBrownianAugmentedFiltration B P hB t) _ (u t) := by
    have hm : @Measurable Ω ((Fin n × Fin 2) → ℝ)
        (ginibreBrownianAugmentedFiltration B P hB t) _
        (fun ω i => d*fderiv ℝ f (X t ω) (ginibreCoordinateDirection i)) :=
      @Measurable.of_eval Ω (Fin n × Fin 2) (fun _ => ℝ)
        (ginibreBrownianAugmentedFiltration B P hB t) _ _
        (fun i => (((hG i).1 t).measurable).const_mul d)
    exact (PiLp.continuous_toLp 2 _).measurable.comp hm
  have hui (t : ℝ≥0) (i : Fin n × Fin 2) : MemLp (fun ω => u t ω i) 2 P := by
    have hm := (((hG i).1 t).measurable).mono ((ginibreBrownianAugmentedFiltration B P hB).le t)
        le_rfl
    exact (MemLp.of_bound hm.aestronglyMeasurable C (ae_of_all P ((hG i).2.2 t))).const_mul d
  have huc : ∀ᵐ ω ∂P, ContinuousOn (fun t => u t ω) (Ioi 0) := by
    apply ae_of_all
    intro ω
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    exact continuous_const.mul ((hG i).2.1 ω)
  have hb (t ω i) : ‖u t ω i‖ ≤ |d| * C := by
    change ‖d*fderiv ℝ f (X t ω) (ginibreCoordinateDirection i)‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hG i).2.2 t ω) (abs_nonneg d)
  apply brownianUnitShiftedUniformSum_punctured_tendstoInMeasure_of_horizon_limits B P hB hind u hum
      hui huc
    (|d| * C) (mul_nonneg (abs_nonneg _) hC) hb a r _ _
  · convert hJ (a+r) har using 1
    funext k ω
    exact ginibreConfigurationBrownianGradientField_sum_eq n α B X f (a+r) k ω
  · convert hJ a ((le_add_of_nonneg_right (bot_le : 0 ≤ r)).trans har) using 1
    funext k ω
    exact ginibreConfigurationBrownianGradientField_sum_eq n α B X f a k ω

end
end GinibrePoincare
