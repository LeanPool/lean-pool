/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreLinearStatisticPoincare.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreLinearStatisticDifferential
public import LeanPool.GinibrePoincare.Analysis.EquilibriumProbability
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Ginibre linear statistic Poincare

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `ginibreLinearStatistic_poincare`, `ginibreLinearStatisticMeasure_identity`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ContDiff NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The law of the linear statistic `∑ i, g (z i)` under the Ginibre measure. -/
def ginibreLinearStatisticMeasure (n : ℕ) (g : ℂ → ℂ) : Measure ℂ :=
  (ginibreMeasure n).map (ginibreLinearStatistic n g)

/-- Sharp dimension-free Poincaré transfer for every actual C¹ Lipschitz
linear statistic, on its literal pushforward law. -/
theorem ginibreLinearStatistic_poincare {n : ℕ} (hn : 0 < n)
    (g : ℂ → ℂ) (hg : ContDiff ℝ 1 g) (K : ℝ≥0) (hLip : LipschitzWith K g)
    (F : ℂ → ℝ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    (∫ w, (F w-(∫ v, F v ∂ginibreLinearStatisticMeasure n g))^2 ∂ginibreLinearStatisticMeasure n g)
        ≤
      ((K : ℝ)^2/2)*(∫ w, ‖fderiv ℝ F w‖^2 ∂ginibreLinearStatisticMeasure n g) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let G := ginibreLinearStatistic n g
  let f := fun z => F (G z)
  have hG : ContDiff ℝ 1 G := ginibreLinearStatistic_contDiff g hg
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by simp)
  have hf : ContDiff ℝ 1 f := hF1.comp hG
  let Fb := ofCompactSupport F hF.continuous hc
  let Db := ofCompactSupport (fun w => ‖fderiv ℝ F w‖)
    (hF.continuous_fderiv (by simp)).norm (hc.fderiv ℝ).norm
  have hfb : ∀ z, ‖f z‖≤‖Fb‖ := fun z => Fb.norm_coe_le_norm (G z)
  have hDb : ∀ w, ‖fderiv ℝ F w‖≤‖Db‖ := fun w => by
    have hh := Db.norm_coe_le_norm w
    change ‖‖fderiv ℝ F w‖‖≤‖Db‖ at hh
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hh
  have hfl : MemLp f 2 (ginibreMeasure n) := MemLp.of_bound hf.continuous.aestronglyMeasurable ‖Fb‖
      (ae_of_all _ hfb)
  have hpb (z : Configuration n) : ‖ginibreEuclideanGradient f z‖^2 ≤
      (n : ℝ)*(K : ℝ)^2*‖Db‖^2 := by
    rw [ginibreEuclideanGradient_norm_sq]
    exact (ginibreLinearStatistic_gradient_bound g hg K hLip F hF1 z).trans
      (mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)|>.mpr (hDb (G z))) (by
          positivity))
  have hgb (z : Configuration n) : ‖ginibreEuclideanGradient f z‖≤Real.sqrt ((n : ℝ)*(K :
      ℝ)^2*‖Db‖^2) := by
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (hpb z)
  have hgc : Continuous (ginibreEuclideanGradient f) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n × Fin 2 => ℝ)).comp
    apply continuous_pi
    intro k
    by_cases h : k.2=0
    · simpa only [h, ite_true] using (hf.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const (y := realCoordinateDirection k.1))
    · simpa only [h, ite_false] using (hf.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const (y := imaginaryCoordinateDirection k.1))
  have hgl : MemLp (ginibreEuclideanGradient f) 2 (ginibreMeasure n) :=
    MemLp.of_bound hgc.aestronglyMeasurable
      (Real.sqrt ((n : ℝ)*(K : ℝ)^2*‖Db‖^2)) (ae_of_all _ hgb)
  have hs : ∀ σ : Fin n ≃ Fin n, ∀ z, f (z ∘ σ)=f z := by
    intro σ z
    change F (∑ i, g (z (σ i)))=F (∑ i, g (z i))
    exact congrArg F (Equiv.sum_comp σ (fun i => g (z i)))
  have hP := ginibre_C1_finite_energy_poincare hn f hf hs hfl hgl
  have hD : Integrable (fun z => ‖fderiv ℝ F (G z)‖^2) (ginibreMeasure n) := by
    apply Integrable.mono' (integrable_const (‖Db‖^2))
      (((hF.continuous_fderiv (by simp)).comp hG.continuous).norm.pow 2).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hDb (G z))
  have hE : (∫ z, realGradientNormSq f z ∂ginibreMeasure n) ≤
      (n : ℝ)*(K : ℝ)^2*(∫ z, ‖fderiv ℝ F (G z)‖^2 ∂ginibreMeasure n) := by
    rw [← integral_const_mul]
    apply integral_mono
    · simpa only [ginibreEuclideanGradient_norm_sq] using hgl.norm.integrable_sq
    · exact hD.const_mul _
    · exact fun z => ginibreLinearStatistic_gradient_bound g hg K hLip F hF1 z
  have hR : smoothGinibreVariance n f ≤ ((K : ℝ)^2/2)*(∫ z, ‖fderiv ℝ F (G z)‖^2 ∂ginibreMeasure n)
      := by
    have hnR : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
    calc
      _ ≤ (1/(2*(n : ℝ)))*(∫ z, realGradientNormSq f z ∂ginibreMeasure n) := hP
      _ ≤ (1/(2*(n : ℝ)))*((n : ℝ)*(K : ℝ)^2*(∫ z, ‖fderiv ℝ F (G z)‖^2 ∂ginibreMeasure n)) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
      _ = _ := by field_simp
  have hmean : (∫ w, F w ∂ginibreLinearStatisticMeasure n g)=∫ z, f z ∂ginibreMeasure n :=
    integral_map hG.continuous.measurable.aemeasurable hF.continuous.aestronglyMeasurable
  have hv : (∫ w, (F w-(∫ v, F v ∂ginibreLinearStatisticMeasure n g))^2
      ∂ginibreLinearStatisticMeasure n g)=smoothGinibreVariance n f := by
    calc
      _ = ∫ z, (F (G z)-(∫ v, F v ∂ginibreLinearStatisticMeasure n g))^2 ∂ginibreMeasure n :=
        integral_map hG.continuous.measurable.aemeasurable
          (((hF.continuous.sub (continuous_const (y := ∫ v, F v ∂ginibreLinearStatisticMeasure n
              g))).pow 2).aestronglyMeasurable)
      _ = _ := by rw [hmean]; rfl
  have he : (∫ w, ‖fderiv ℝ F w‖^2 ∂ginibreLinearStatisticMeasure n g)=
      ∫ z, ‖fderiv ℝ F (G z)‖^2 ∂ginibreMeasure n :=
    integral_map hG.continuous.measurable.aemeasurable
      ((hF.continuous_fderiv (by simp)).norm.pow 2).aestronglyMeasurable
  rw [hv, he]
  exact hR

/-- The identity statistic has the exact standard complex Gaussian law. -/
theorem ginibreLinearStatisticMeasure_identity {n : ℕ} (hn : 0 < n) :
    ginibreLinearStatisticMeasure n id=standardComplexGaussianMeasure := by
  exact coordinateSum_ginibre_gaussian n hn

end
end GinibrePoincare
