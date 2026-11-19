/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalConfigurationProcess.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalVectorProcess
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianProjection
public import LeanPool.GinibrePoincare.Analysis.GaussianFourierCoordinates
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalExistence
public import LeanPool.GinibrePoincare.Analysis.GaussianHermiteMoments
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation

/-!
# Brownian orthogonal configuration process

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianConfigurationGrouping_symm_apply_zero`,
`brownianConfigurationGrouping_symm_apply_one`,
`brownianFamily_actual_center_recenter_noise_independent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The continuous linear equivalence between real coordinates
`EuclideanSpace ℝ (Fin n × Fin 2)` and `GinibreRealEuclidean n`, passing through
`Configuration n`. -/
def brownianConfigurationGrouping (n : ℕ) :
    EuclideanSpace ℝ (Fin n × Fin 2) ≃L[ℝ] GinibreRealEuclidean n :=
  (configurationEuclideanEquiv n).symm.trans (ginibreConfigToEuclidean n)

@[simp] theorem brownianConfigurationGrouping_apply (n : ℕ)
    (v : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n) :
    brownianConfigurationGrouping n v i = ⟨v (i, 0), v (i, 1)⟩ := by
  simp [brownianConfigurationGrouping]

@[simp] theorem brownianConfigurationGrouping_symm_apply_zero (n : ℕ)
    (x : GinibreRealEuclidean n) (i : Fin n) :
    (brownianConfigurationGrouping n).symm x (i, 0) = (x i).re := by
  change configurationEuclideanEquiv n ((ginibreConfigToEuclidean n).symm x) (i, 0) = _
  rw [configurationEuclideanEquiv_apply_zero]
  rfl

@[simp] theorem brownianConfigurationGrouping_symm_apply_one (n : ℕ)
    (x : GinibreRealEuclidean n) (i : Fin n) :
    (brownianConfigurationGrouping n).symm x (i, 1) = (x i).im := by
  change configurationEuclideanEquiv n ((ginibreConfigToEuclidean n).symm x) (i, 1) = _
  rw [configurationEuclideanEquiv_apply_one]
  rfl

theorem brownianConfigurationGrouping_inner (n : ℕ)
    (x : GinibreRealEuclidean n) (v : EuclideanSpace ℝ (Fin n × Fin 2)) :
    inner ℝ x (brownianConfigurationGrouping n v) =
      inner ℝ ((brownianConfigurationGrouping n).symm x) v := by
  simp [PiLp.inner_apply, Complex.inner, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem brownianConfigurationGrouping_inner_symm (n : ℕ)
    (x y : GinibreRealEuclidean n) :
    inner ℝ ((brownianConfigurationGrouping n).symm x)
      ((brownianConfigurationGrouping n).symm y) = inner ℝ x y := by
  rw [← brownianConfigurationGrouping_inner, ContinuousLinearEquiv.apply_symm_apply]

/-- The original independent real coordinate Brownian motions, grouped into
complex coordinates, form the actual standard configuration Brownian process. -/
theorem brownianFamily_grouped_isBrownianVectorProcess {Ω : Type*}
    [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IsBrownianVectorProcess (fun t ω => brownianConfigurationGrouping n
      (WithLp.toLp 2 (fun i => B i t ω))) P := by
  have hV := brownianFamily_toEuclidean_isBrownianVectorProcess B P hB hind
  refine ⟨⟨hV.gaussian.comp_left (fun _ => (brownianConfigurationGrouping
      n).toContinuousLinearMap),?_,⟩,?_,?_⟩
  · intro s t x y
    simp only [brownianConfigurationGrouping_inner]
    rw [hV.covariance, brownianConfigurationGrouping_inner_symm]
  · filter_upwards [hV.continuous] with ω hω
    exact (brownianConfigurationGrouping n).continuous.comp hω
  · filter_upwards [hV.zero_start] with ω hω
    simp [hω]

/-- The literal original driving noise has independent center and recentered
whole paths, with the paper's diffusion scaling. -/
theorem brownianFamily_actual_center_recenter_noise_independent {Ω : Type*}
    [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) :
    IndepFun (fun ω t => projectToCenterLine n (ginibreConfigurationBrownianNoise n B α ω t))
      (fun ω t => recenteredConfiguration n (ginibreConfigurationBrownianNoise n B α ω t)) P := by
  let V := fun t ω => brownianConfigurationGrouping n (WithLp.toLp 2 (fun i => B i t ω))
  have hV := brownianFamily_grouped_isBrownianVectorProcess n B P hB hind
  have hi := ginibreGaussianNoise_center_recenter_independent n hV
  let σ := Real.sqrt (2*α/(n : ℝ)^2)
  let H : (ℝ≥0 → GinibreRealEuclidean n) → ℝ → Configuration n :=
    fun y t => σ • (ginibreConfigToEuclidean n).symm (y t.toNNReal)
  have hH : Measurable H := by
    apply Measurable.of_eval
    intro t
    exact (((ginibreConfigToEuclidean n).symm.continuous.measurable.comp
      (measurable_pi_apply t.toNNReal)).const_smul σ)
  have hh := hi.comp hH hH
  have hnoise (ω : Ω) (t : ℝ) : ginibreConfigurationBrownianNoise n B α ω t =
      σ • (ginibreConfigToEuclidean n).symm (V t.toNNReal ω) := by
    ext i
    apply Complex.ext <;> simp [ginibreConfigurationBrownianNoise, σ, V,
      brownianConfigurationGrouping_apply, ginibreConfigToEuclidean, Complex.mul_re, Complex.mul_im]
  have hcenter (ω : Ω) (t : ℝ) :
      H (fun u => ginibreCenterProjectionEuclidean n (V u ω)) t =
      projectToCenterLine n (ginibreConfigurationBrownianNoise n B α ω t) := by
    rw [hnoise]
    change σ • (ginibreConfigToEuclidean n).symm
      (ginibreCenterProjectionEuclidean n (V t.toNNReal ω)) = _
    rw [ginibreCenterProjectionEuclidean_apply]
    simpa only [ginibreConfigToEuclidean, ContinuousLinearEquiv.symm_symm,
        PiLp.coe_continuousLinearEquiv, WithLp.ofLp_toLp,
      ginibreCenterProjectionCLM_apply] using
      (map_smul (ginibreCenterProjectionCLM n) σ (WithLp.ofLp (V t.toNNReal ω))).symm
  have hrecenter (ω : Ω) (t : ℝ) :
      H (fun u => ginibreRecenterProjectionEuclidean n (V u ω)) t =
      recenteredConfiguration n (ginibreConfigurationBrownianNoise n B α ω t) := by
    rw [hnoise]
    change σ • (ginibreConfigToEuclidean n).symm
      (ginibreRecenterProjectionEuclidean n (V t.toNNReal ω)) = _
    rw [ginibreRecenterProjectionEuclidean_apply]
    simpa only [ginibreConfigToEuclidean, ContinuousLinearEquiv.symm_symm,
        PiLp.coe_continuousLinearEquiv, WithLp.ofLp_toLp,
      recenteredCLM_apply] using
      (map_smul (recenteredCLM n) σ (WithLp.ofLp (V t.toNNReal ω))).symm
  convert hh using 1
  · funext ω t
    exact (hcenter ω t).symm
  · funext ω t
    exact (hrecenter ω t).symm

end
end GinibrePoincare
