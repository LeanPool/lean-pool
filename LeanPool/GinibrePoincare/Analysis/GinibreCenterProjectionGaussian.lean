/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreCenterProjectionGaussian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreCenterProjectionClasses
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarWeakEquality

/-!
# Ginibre center projection Gaussian

Part of the ginibre measure and holomorphic geometry development of the
Ginibre Poincaré formalization.

Main results: `ginibreConjugateCenterTransform_firstMode`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- The normalized actual Gaussian class `V * conjugate S`. -/
def ginibreConjugateCenterTransformL2 (n : ℕ) (hn : 0 < n) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  normalizedVandermondeL2 n hn (star (ginibreCenterSumL2 n hn))

/-- Equation (2.38), with the right side zero by (2.39): the Gaussian
holomorphic projection of `V * conjugate S` vanishes. -/
theorem ginibreConjugateCenterTransform_zeroMode (n : ℕ) (hn : 0 < n) :
    gaussianHermiteMode hn 0 (ginibreConjugateCenterTransformL2 n hn) = 0 := by
  let U := vandermondeSymmetricAlternatingEquiv n hn
  let t := ginibreSymmetricConjugationEquiv n (ginibreCoordinateSumPowerL2 n hn 1)
  let G := ginibreConjugateCenterTransformL2 n hn
  let G0 := gaussianHermiteMode hn 0 G
  have htval : t.val = star (ginibreCenterSumL2 n hn) := rfl
  have hUG : (U t).val = G := rfl
  have hGalt : G ∈ gaussianAlternatingL2 n := by rw [← hUG]; exact (U t).property
  have hG0alt : G0 ∈ gaussianAlternatingL2 n :=
    gaussianHermiteMode_mem_alternating hn 0 hGalt
  let v : gaussianAlternatingL2 n := ⟨G0, hG0alt⟩
  let h := U.symm v
  have hv : v ∈ gaussianAlternatingZeroModeClosedSpan n hn := by
    change v ∈ (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule
    rw [gaussianAlternatingZeroModeClosedSpan_eq_hermiteZeroMode_comap]
    exact gaussianHermiteMode_mem_closedSpan hn 0 G
  have hh : h ∈ ginibreSymmetricHolomorphicPolynomialClosedSpan n hn := by
    have him : v ∈ (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule.map
        U.toLinearMap := by
      rw [map_ginibreSymmetricHolomorphicPolynomialClosedSpan]
      exact hv
    obtain ⟨w, hw, heq⟩ := him
    have heqh : w = h := by
      apply U.injective
      exact heq.trans (U.apply_symm_apply v).symm
    exact heqh ▸ hw
  have hhamb : h.val ∈ ginibreHolomorphicAmbientClosedSpan n hn := ⟨h, hh, rfl⟩
  have hinner : inner ℂ G G0 = 0 := by
    have hip := Submodule.starProjection_inner_eq_zero (star (ginibreCenterSumL2 n hn))
      h.val hhamb
    rw [ginibreCenterSumL2_conjugateProjection_zero, sub_zero] at hip
    have hhU : U h = v := U.apply_symm_apply v
    have hm := U.inner_map_map t h
    change inner ℂ (U t).val (U h).val = inner ℂ t.val h.val at hm
    rw [hUG, hhU, htval] at hm
    exact hm.trans hip
  have hr := Submodule.starProjection_inner_eq_zero G G0
    (gaussianHermiteMode_mem_closedSpan hn 0 G)
  change inner ℂ (G - hermiteAntiDegreeProjection n hn 0 G) G0 = 0 at hr
  rw [← gaussianHermiteMode_eq_antiDegreeProjection] at hr
  change inner ℂ (G - G0) G0 = 0 at hr
  rw [inner_sub_left, hinner, zero_sub, neg_eq_zero] at hr
  exact inner_self_eq_zero.mp hr

theorem ginibreConjugateCenterTransform_ae (n : ℕ) (hn : 0 < n) :
    (ginibreConjugateCenterTransformL2 n hn : Configuration n → ℂ)
      =ᵐ[complexGaussianMeasure n]
      fun z => normalizedVandermondeMultiplier n z * conj (coordinateSum z) := by
  have hs := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq (ginibreCenterSumL2_ae n hn)
  have hstar := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq (Lp.coeFn_star (ginibreCenterSumL2 n hn))
  filter_upwards [normalizedVandermondeL2_coeFn_public n hn (star (ginibreCenterSumL2 n hn)),
    hs, hstar] with z hU hs hstar
  change (normalizedVandermondeL2 n hn (star (ginibreCenterSumL2 n hn))) z = _
  rw [hU, hstar]
  change normalizedVandermondeMultiplier n z * conj (ginibreCenterSumL2 n hn z) = _
  rw [hs]

theorem dbarComponent_conjugate_coordinateSum {n : ℕ} (j : Fin n)
    (z : Configuration n) : dbarComponent (fun w => conj (coordinateSum w)) j z = 1 := by
  let T : Configuration n →L[ℝ] ℂ :=
    Complex.conjCLE.toContinuousLinearMap.comp (coordinateSumCLM n)
  have heq : (T : Configuration n → ℂ) = fun w => conj (coordinateSum w) := by
    funext w
    simp [T]
  rw [← heq, dbarComponent, T.fderiv]
  simp [T, realCoordinateDirection, imaginaryCoordinateDirection,
    coordinateSum_coordinateDirection, coordinateSumCLM_apply]
  ring

/-- The true coordinate weak derivatives of the conjugate-center transform
are all the normalized Vandermonde ground state. -/
theorem ginibreConjugateCenterTransform_weakDbar (n : ℕ) (hn : 0 < n) (j : Fin n) :
    IsGaussianWeakDbar n (ginibreConjugateCenterTransformL2 n hn)
      (normalizedVandermondeGroundStateL2 n hn) j := by
  let F : Configuration n → ℂ := fun z =>
    normalizedVandermondeMultiplier n z * conj (coordinateSum z)
  have hS : ContDiff ℝ 1 (fun z : Configuration n => conj (coordinateSum z)) := by
    have h : ContDiff ℝ 1 (fun z => conj (coordinateSumCLM n z)) :=
      Complex.conjCLE.contDiff.comp (coordinateSumCLM n).contDiff
    simpa only [coordinateSumCLM_apply] using h
  have hM : ContDiff ℝ 1 (normalizedVandermondeMultiplier n) :=
    contDiff_const.mul ((contDiff_vandermonde n).of_le (by simp))
  apply gaussian_smooth_weak_dbar hn j _ _ F (hM.mul hS)
    (ginibreConjugateCenterTransform_ae n hn)
  have hd (z : Configuration n) : dbarComponent F j z = normalizedVandermondeMultiplier n z := by
    rw [dbarComponent_mul (hM.differentiable (by norm_num)) (hS.differentiable (by norm_num))]
    have hmzero : dbarComponent (normalizedVandermondeMultiplier n) j z = 0 := by
      exact dbarComponent_eq_zero_of_differentiable_complex
        ((differentiable_vandermonde n).const_mul _) j z
    rw [hmzero, dbarComponent_conjugate_coordinateSum, zero_mul, mul_one, zero_add]
  exact (normalizedVandermondeGroundStateL2_coeFn n hn).trans
    (Filter.Eventually.of_forall fun z => (hd z).symm)

/-- The conjugate-center Gaussian class has unit squared norm. -/
theorem ginibreConjugateCenterTransform_norm_sq (n : ℕ) (hn : 0 < n) :
    ‖ginibreConjugateCenterTransformL2 n hn‖ ^ 2 = 1 := by
  rw [ginibreConjugateCenterTransformL2, (normalizedVandermondeL2 n hn).norm_map]
  have hnorm : ‖star (ginibreCenterSumL2 n hn)‖ = ‖ginibreCenterSumL2 n hn‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    exact congrArg ENNReal.toReal AEEqFun.eLpNorm_star
  rw [hnorm]
  simpa [ginibreCenterSumL2] using ginibreCoordinateSumPowerL2_norm_sq n hn 1

/-- The actual normalized Vandermonde ground state has unit squared norm. -/
theorem normalizedVandermondeGroundState_norm_sq (n : ℕ) (hn : 0 < n) :
    ‖normalizedVandermondeGroundStateL2 n hn‖ ^ 2 = 1 := by
  let := ginibreProbabilityInstance hn
  have hconst : (ginibreConstantL2 n hn 1 : Configuration n → ℂ)
      =ᵐ[complexGaussianMeasure n] fun _ => (1 : ℂ) := by
    exact (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
      (ginibreMassEvaluation n hn)).ae_eq
      (Lp.coeFn_const (2 : ℝ≥0∞) (ginibreMeasure n) (1 : ℂ))
  have heq : normalizedVandermondeGroundStateL2 n hn =
      normalizedVandermondeL2 n hn (ginibreConstantL2 n hn 1) := by
    apply Lp.ext
    filter_upwards [normalizedVandermondeGroundStateL2_coeFn n hn,
      normalizedVandermondeL2_coeFn_public n hn (ginibreConstantL2 n hn 1), hconst]
      with z hV hU hc
    rw [hV, hU, hc, mul_one]
  rw [heq, (normalizedVandermondeL2 n hn).norm_map, (ginibreConstantL2 n hn).norm_map]
  norm_num

/-- The exact equality in the Gaussian Hörmander--Berndtsson estimate for
`V * conjugate S`, completing Remark 2.8's equality calculation. -/
theorem ginibreConjugateCenterTransform_gap_equality (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * ∑ _ : Fin n, ‖normalizedVandermondeGroundStateL2 n hn‖ ^ 2 =
      ‖ginibreConjugateCenterTransformL2 n hn‖ ^ 2 -
        ‖gaussianHermiteMode hn 0 (ginibreConjugateCenterTransformL2 n hn)‖ ^ 2 := by
  rw [ginibreConjugateCenterTransform_zeroMode, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    sub_zero, ginibreConjugateCenterTransform_norm_sq]
  simp [normalizedVandermondeGroundState_norm_sq, hn.ne']

/-- There are no antiholomorphic components of degree at least two. -/
theorem ginibreConjugateCenterTransform_higherMode_zero (n : ℕ) (hn : 0 < n)
    (d : ℕ) (hd : 2 ≤ d) :
    gaussianHermiteMode hn d (ginibreConjugateCenterTransformL2 n hn) = 0 :=
  (gaussianWeakDbar_gap_equality_iff hn (ginibreConjugateCenterTransformL2 n hn)
    (fun _ => normalizedVandermondeGroundStateL2 n hn)
    (ginibreConjugateCenterTransform_weakDbar n hn)).mp
      (ginibreConjugateCenterTransform_gap_equality n hn) d hd

/-- Equation (2.40)'s actual first antiholomorphic Hermite-space membership. -/
theorem ginibreConjugateCenterTransform_firstMode (n : ℕ) (hn : 0 < n) :
    ginibreConjugateCenterTransformL2 n hn ∈ hermiteAntiDegreeClosedSpan n hn 1 := by
  have hsum := tsum_gaussianHermiteMode hn (ginibreConjugateCenterTransformL2 n hn)
  have hs : (∑' d : ℕ, gaussianHermiteMode hn d (ginibreConjugateCenterTransformL2 n hn)) =
      gaussianHermiteMode hn 1 (ginibreConjugateCenterTransformL2 n hn) := by
    apply tsum_eq_single 1
    intro d hd
    by_cases h0 : d = 0
    · subst d
      exact ginibreConjugateCenterTransform_zeroMode n hn
    · exact ginibreConjugateCenterTransform_higherMode_zero n hn d (by omega)
  rw [hs] at hsum
  rw [← hsum]
  exact gaussianHermiteMode_mem_closedSpan hn 1 _

end
end GinibrePoincare

