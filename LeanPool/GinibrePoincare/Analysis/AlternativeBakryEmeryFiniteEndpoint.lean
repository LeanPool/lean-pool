/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryFiniteEndpoint.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinGlobal
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryPolygonalResponse
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGaussianResponse
/-! Actual finite Gaussian polygonal-Langevin endpoint laws and their sharp LSI.
The corrected trajectories are selected from the internally proved global
existence theorem; no trajectory or entropy certificate is supplied. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual finite-time state driven by a finite variance-one Gaussian family. -/
def bakryEmeryFiniteEndpoint
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (m : ℕ) (h : ℝ) (hh : 0 < h)
    (x : EuclideanSpace ℝ (Fin m × ι)) : EuclideanSpace ℝ ι :=
  let N := fun s => Real.sqrt 2 • bakryEmeryPolygonalNoise m h x.ofLp s
  let Y := bakryEmeryLangevinCorrectionOn W κ hκ hW hc N
    ((bakryEmeryPolygonalNoise_continuous m h x.ofLp).const_smul (Real.sqrt 2))
    z ((m : ℝ)*h) (by positivity)
  Y ((m : ℝ)*h)+N ((m : ℝ)*h)

private theorem covariance_nonneg (κ : ℝ) (hκ : 0 < κ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ bakryEmeryResponseCovariance κ t := by
  unfold bakryEmeryResponseCovariance
  apply div_nonneg
  · have he : Real.exp (-2*κ*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  · positivity

omit [DecidableEq ι] in
/-- The selected actual endpoint is Lipschitz with the exact dissipative response
coefficient, even though differentiability of the selected flow is unnecessary. -/
theorem bakryEmeryFiniteEndpoint_lipschitz
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (m : ℕ) (h : ℝ) (hh : 0 < h) :
    LipschitzWith (Real.toNNReal (Real.sqrt (2*bakryEmeryResponseCovariance κ ((m : ℝ)*h))))
      (bakryEmeryFiniteEndpoint W κ hκ hW hc z m h hh) := by
  classical
  have hT : 0 ≤ (m : ℝ)*h := by positivity
  have hq := covariance_nonneg κ hκ ((m : ℝ)*h) hT
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let N := fun a : EuclideanSpace ℝ (Fin m × ι) =>
    fun s => Real.sqrt 2 • bakryEmeryPolygonalNoise m h a.ofLp s
  let Y := fun a : EuclideanSpace ℝ (Fin m × ι) =>
    bakryEmeryLangevinCorrectionOn W κ hκ hW hc (N a)
      ((bakryEmeryPolygonalNoise_continuous m h a.ofLp).const_smul (Real.sqrt 2))
      z ((m : ℝ)*h) hT
  have hx := bakryEmeryLangevinCorrectionOn_spec W κ hκ hW hc (N x)
    ((bakryEmeryPolygonalNoise_continuous m h x.ofLp).const_smul (Real.sqrt 2))
    z ((m : ℝ)*h) hT
  have hy := bakryEmeryLangevinCorrectionOn_spec W κ hκ hW hc (N y)
    ((bakryEmeryPolygonalNoise_continuous m h y.ofLp).const_smul (Real.sqrt 2))
    z ((m : ℝ)*h) hT
  have hb := bakryEmeryLangevin_polygonal_noise_response W κ hκ
    (hW.differentiable (by norm_num)) hc m h hh (Real.sqrt 2) x.ofLp y.ofLp
    (Y y) (Y x) hy.1.continuousOn hx.1.continuousOn (hx.2.1.trans hy.2.1.symm)
    hy.2.2.2 hx.2.2.2
  change ‖bakryEmeryFiniteEndpoint W κ hκ hW hc z m h hh x-
    bakryEmeryFiniteEndpoint W κ hκ hW hc z m h hh y‖ ≤ _*‖x-y‖
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  change ‖bakryEmeryFiniteEndpoint W κ hκ hW hc z m h hh x-
    bakryEmeryFiniteEndpoint W κ hκ hW hc z m h hh y‖^2 ≤
      ((Real.sqrt 2)^2*bakryEmeryResponseCovariance κ ((m : ℝ)*h))*‖x-y‖^2 at hb
  rw [hs] at hb
  rw [Real.toNNReal_of_nonneg (Real.sqrt_nonneg _)]
  have hs' := Real.sq_sqrt (show 0 ≤ 2*bakryEmeryResponseCovariance κ ((m : ℝ)*h) by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, hs']
  exact hb

omit [DecidableEq ι] in
/-- Sharp entropy inequality for the actual finite-noise endpoint observable. -/
theorem bakryEmeryFiniteEndpoint_square_lsi [Nonempty ι]
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (m : ℕ) (hm : 0 < m) (h : ℝ) (hh : 0 < h)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hfL : LipschitzWith L f) (C : ℝ) (hfC : ∀ y, |f y| ≤ C) :
    squareEntropy (Measure.pi (fun _ : Fin m × ι => gaussianReal 0 1))
      (fun x => f (bakryEmeryFiniteEndpoint W κ hκ hW hc z m h hh (WithLp.toLp 2 x))) ≤
      (4*bakryEmeryResponseCovariance κ ((m : ℝ)*h))*
      ∫ x, ‖gradient f (bakryEmeryFiniteEndpoint W κ hκ hW hc z m h hh
        (WithLp.toLp 2 x))‖^2
        ∂Measure.pi (fun _ : Fin m × ι => gaussianReal 0 1) := by
  classical
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hq := covariance_nonneg κ hκ ((m : ℝ)*h) (by positivity)
  let K := Real.toNNReal (Real.sqrt (2*bakryEmeryResponseCovariance κ ((m : ℝ)*h)))
  have hk : (K : ℝ)^2=2*bakryEmeryResponseCovariance κ ((m : ℝ)*h) := by
    dsimp [K]
    rw [max_eq_left (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  have hb := bakryEmeryGaussianResponse_square_lsi (I := Fin m × ι) 1 (by norm_num)
    (bakryEmeryFiniteEndpoint W κ hκ hW hc z m h hh)
    (bakryEmeryFiniteEndpoint_lipschitz W κ hκ hW hc z m h hh)
    f hf hfL C hfC
  have hk' : ((Real.toNNReal (Real.sqrt (2*bakryEmeryResponseCovariance κ ((m : ℝ)*h)))) : ℝ)^2 =
      2*bakryEmeryResponseCovariance κ ((m : ℝ)*h) := hk
  rw [hk'] at hb
  convert hb using 1; simp only [NNReal.coe_one]; ring

/-- The actual finite Gaussian-driven endpoint distribution. -/
def bakryEmeryFiniteEndpointLaw
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (m : ℕ) (h : ℝ) (hh : 0 < h) : Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi (fun _ : Fin m × ι => gaussianReal 0 1)).map
    (fun x => bakryEmeryFiniteEndpoint W κ hκ hW hc z m h hh (WithLp.toLp 2 x))

omit [DecidableEq ι] in
theorem bakryEmeryFiniteEndpointLaw_probability
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (m : ℕ) (h : ℝ) (hh : 0 < h) :
    IsProbabilityMeasure (bakryEmeryFiniteEndpointLaw W κ hκ hW hc z m h hh) := by
  classical
  unfold bakryEmeryFiniteEndpointLaw
  infer_instance

omit [DecidableEq ι] in
/-- Sharp LSI of the actual finite-noise endpoint probability law. -/
theorem bakryEmeryFiniteEndpointLaw_square_lsi [Nonempty ι]
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (m : ℕ) (hm : 0 < m) (h : ℝ) (hh : 0 < h)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hfL : LipschitzWith L f) (C : ℝ) (hfC : ∀ y, |f y| ≤ C) :
    squareEntropy (bakryEmeryFiniteEndpointLaw W κ hκ hW hc z m h hh) f ≤
      (4*bakryEmeryResponseCovariance κ ((m : ℝ)*h))*
        ∫ x, ‖gradient f x‖^2 ∂bakryEmeryFiniteEndpointLaw W κ hκ hW hc z m h hh := by
  classical
  have hΦ := (bakryEmeryFiniteEndpoint_lipschitz W κ hκ hW hc z m h hh).continuous.comp
    (PiLp.continuous_toLp 2 (fun _ : Fin m × ι => ℝ))
  change Continuous (fun x => bakryEmeryFiniteEndpoint W κ hκ hW hc z m h hh
    (WithLp.toLp 2 x)) at hΦ
  have hgrad : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  unfold bakryEmeryFiniteEndpointLaw
  rw [squareEntropy_map _ _ hΦ.measurable.aemeasurable f
    (hf.continuous.pow 2).aestronglyMeasurable
    (continuous_square_mul_log hf.continuous).aestronglyMeasurable,
    integral_map hΦ.measurable.aemeasurable
      (show AEStronglyMeasurable (fun x => ‖gradient f x‖^2) _ from
        (hgrad.norm.pow 2).aestronglyMeasurable)]
  exact bakryEmeryFiniteEndpoint_square_lsi W κ hκ hW hc z m hm h hh f hf hfL C hfC

omit [DecidableEq ι] in
/-- The finite-noise endpoint LSI has the uniform Bakry–Émery constant `2/κ`,
independently of the time horizon and grid size. -/
theorem bakryEmeryFiniteEndpointLaw_uniform_square_lsi [Nonempty ι]
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (m : ℕ) (hm : 0 < m) (h : ℝ) (hh : 0 < h)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hfL : LipschitzWith L f) (C : ℝ) (hfC : ∀ y, |f y| ≤ C) :
    squareEntropy (bakryEmeryFiniteEndpointLaw W κ hκ hW hc z m h hh) f ≤
      (2/κ)*∫ x, ‖gradient f x‖^2 ∂bakryEmeryFiniteEndpointLaw W κ hκ hW hc z m h hh := by
  classical
  have hb := bakryEmeryFiniteEndpointLaw_square_lsi W κ hκ hW hc z m hm h hh f hf hfL C hfC
  have hq : bakryEmeryResponseCovariance κ ((m : ℝ)*h) ≤ 1/(2*κ) := by
    unfold bakryEmeryResponseCovariance
    exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_nonneg _)) (by positivity)
  have hcoef : 4*bakryEmeryResponseCovariance κ ((m : ℝ)*h) ≤ 2/κ := by
    calc
      _ ≤ 4*(1/(2*κ)) := mul_le_mul_of_nonneg_left hq (by norm_num)
      _ = _ := by field_simp; ring
  exact hb.trans (mul_le_mul_of_nonneg_right hcoef (integral_nonneg (fun _ => sq_nonneg _)))

end
end GinibrePoincare
