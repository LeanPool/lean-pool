/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianDbarWeakDomain.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarVolumeDistributions
public import LeanPool.GinibrePoincare.Analysis.GinibreSpatialCutoffs
public import LeanPool.GinibrePoincare.Analysis.HermiteSecondDbarWeakClosure
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-! # Ordinary weak derivatives and Hermite lowering coefficients

The weak derivative is independently defined using compact distributional tests.
To test it against a Hermite polynomial, this module multiplies that polynomial
by expanding spatial cutoffs. Dominated convergence removes the cutoff, while
the derivative-of-cutoff term vanishes. The Gaussian formal adjoint acts by
raising the Hermite index, giving the coefficient relation for the derivative.

For the reverse implication, finite Hermite approximations converge in both
value and derivative L² norms. Closedness of the weak graph then recovers the
compact-test identity. These two directions provide uniqueness, simultaneous
finite approximation, and the exact square-summability criterion for existence
of a weak derivative. Thus the coefficient graph is proved equivalent to the
ordinary distributional graph rather than used as its definition.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff ComplexConjugate BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- Expanding spatial cutoffs converge in every integrable complex pairing. -/
theorem integral_gaussianSpatialCutoff_tendsto {n : ℕ}
    (a : Configuration n → ℂ) (ha : Integrable a (complexGaussianMeasure n)) :
    Tendsto (fun m => ∫ z, (ginibreSpatialCutoff n m z : ℂ) * a z
      ∂complexGaussianMeasure n) atTop (𝓝 (∫ z, a z ∂complexGaussianMeasure n)) := by
  apply tendsto_integral_of_dominated_convergence (fun z => ‖a z‖)
  · intro m
    exact ((Complex.continuous_ofReal.comp
      (ginibreSpatialCutoff_smooth n m).continuous).aestronglyMeasurable.mul
      ha.aestronglyMeasurable)
  · exact ha.norm
  · intro m
    filter_upwards with z
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ginibreSpatialCutoff_mem_unit n m z).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (ginibreSpatialCutoff_mem_unit n m z).2
  · filter_upwards with z
    simpa using (Complex.continuous_ofReal.tendsto 1 |>.comp
      (ginibreSpatialCutoff_tendsto n z)).mul_const (a z)

/-- The cutoff derivative error vanishes in every integrable complex pairing. -/
theorem integral_gaussianSpatialCutoff_deriv_tendsto {n : ℕ}
    (a : Configuration n → ℂ) (ha : Integrable a (complexGaussianMeasure n)) :
    Tendsto (fun m => ∫ z,
      ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) * a z
      ∂complexGaussianMeasure n) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
  rw [← integral_zero (μ := complexGaussianMeasure n) (G := ℂ)]
  apply tendsto_integral_of_dominated_convergence (fun z => M * ‖a z‖)
  · intro m
    exact ((Complex.continuous_ofReal.comp
      (((sobolevCutoff_smooth m).continuous_deriv (by simp)).comp
        contDiff_configurationNormSq.continuous)).aestronglyMeasurable.mul
      ha.aestronglyMeasurable)
  · exact ha.norm.const_mul M
  · intro m
    filter_upwards with z
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (hM m _).trans (div_le_self hM0 (by have := Nat.cast_nonneg (α := ℝ) m; linarith))
  · filter_upwards with z
    simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp
      (sobolevCutoff_tendsto (configurationNormSq z)).2).mul_const (a z)

theorem dbarComponent_gaussianSpatialCutoff (n m : ℕ) (j : Fin n)
    (z : Configuration n) :
    dbarComponent (fun w => (ginibreSpatialCutoff n m w : ℂ)) j z =
      ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) * z j := by
  have hq := (contDiff_configurationNormSq.differentiable (by simp)).differentiableAt (x := z)
  have hb := ((sobolevCutoff_smooth m).differentiable (by simp)
    (configurationNormSq z)).hasDerivAt
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z (hb.comp_hasFDerivAt z hq.hasFDerivAt)
  change HasFDerivAt (fun w => (ginibreSpatialCutoff n m w : ℂ)) _ z at hd
  unfold dbarComponent
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    smul_apply, smul_eq_mul]
  rw [fderiv_configurationNormSq_apply, fderiv_configurationNormSq_apply]
  have hr : (∑ x : Fin n, (conj (z x) * realCoordinateDirection j x).re) = (z j).re := by
    simp only [realCoordinateDirection, coordinateDirection]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj; simp [hbj]
    · simp
  have hi : (∑ x : Fin n, (conj (z x) * imaginaryCoordinateDirection j x).re) = (z j).im := by
    simp only [imaginaryCoordinateDirection, coordinateDirection]
    rw [Finset.sum_eq_single j]
    · simp [Complex.mul_re]
    · intro b hb hbj; simp [hbj]
    · simp
  rw [hr, hi]
  apply Complex.ext <;> simp <;> ring

/-- The Gaussian formal adjoint on each Hermite mode is exactly raising. -/
theorem gaussianHermite_adjoint_creation_ae (n : ℕ) (hn : 0 < n)
    (j : Fin n) (pq : HermiteMultiIndex n) :
    (fun z => (n : ℂ) * z j * conj (multivariateNormalized n hn pq.1 pq.2 z) -
      dbarComponent (fun w => conj (multivariateNormalized n hn pq.1 pq.2 w)) j z)
      =ᵐ[complexGaussianMeasure n]
    (fun z => (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
      conj (multivariateNormalized n hn (raiseHermiteIndex j pq).1
        (raiseHermiteIndex j pq).2 z)) := by
  filter_upwards [coordinate_mul_multivariateNormalized_creation_ae n hn pq.2 pq.1 j]
    with z hz
  rw [dbarComponent_conj_multivariateNormalized, conj_multivariateNormalized_swap,
    conj_multivariateNormalized_swap]
  simp only [raiseHermiteIndex]
  rw [hz]
  ring

theorem gaussianHermiteCoefficient_eq_integral {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn u pq =
      ∫ z, multivariateNormalized n hn pq.2 pq.1 z * u z ∂complexGaussianMeasure n := by
  rw [gaussianHermiteCoefficient_eq_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multivariateNormalizedL2_coeFn n hn pq.1 pq.2] with z hz
  rw [RCLike.inner_apply, hz, conj_multivariateNormalized_swap]
  ring

/-- The formal adjoint pairing of a compact Hermite cutoff converges to
 the actual raising coefficient for every Gaussian L² function. -/
theorem gaussianHermiteCutoff_adjointIntegral_tendsto {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) (pq : HermiteMultiIndex n) :
    Tendsto (fun m => ∫ z, u z * ((n : ℂ) * z j *
      ((ginibreSpatialCutoff n m z : ℂ) * multivariateNormalized n hn pq.2 pq.1 z) -
      dbarComponent (fun w => (ginibreSpatialCutoff n m w : ℂ) *
        multivariateNormalized n hn pq.2 pq.1 w) j z) ∂complexGaussianMeasure n)
      atTop (𝓝 ((Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq))) := by
  let H := multivariateNormalized n hn pq.2 pq.1
  let B := multivariateNormalized n hn (raiseAt pq.2 j) pq.1
  let κ : ℂ := Real.sqrt (n * (pq.2 j + 1) : ℕ)
  have hH : ContDiff ℝ 1 H := contDiff_multivariateNormalized_real n hn _ _
  have hHlp : MemLp H 2 (complexGaussianMeasure n) := memLp_two_multivariateNormalized n hn _ _
  have hBlp : MemLp B 2 (complexGaussianMeasure n) := memLp_two_multivariateNormalized n hn _ _
  have hBu : Integrable (fun z => κ * (B z * u z)) (complexGaussianMeasure n) :=
    (hBlp.integrable_mul (Lp.memLp u)).const_mul κ
  have hEu : Integrable (fun z => z j * H z * u z) (complexGaussianMeasure n) :=
    (memLp_two_coordinate_mul_multivariateNormalized n hn pq.2 pq.1 j).integrable_mul (Lp.memLp u)
  have hraise : (fun z => (n : ℂ) * z j * H z - dbarComponent H j z)
      =ᵐ[complexGaussianMeasure n] (fun z => κ * B z) := by
    filter_upwards [coordinate_mul_multivariateNormalized_creation_ae n hn pq.2 pq.1 j]
      with z hz
    rw [dbarComponent_multivariateNormalized]
    dsimp [H, B, κ] at *
    rw [hz]
    ring
  have hid (m : ℕ) :
      (∫ z, u z * ((n : ℂ) * z j *
        ((ginibreSpatialCutoff n m z : ℂ) * H z) -
        dbarComponent (fun w => (ginibreSpatialCutoff n m w : ℂ) * H w) j z)
          ∂complexGaussianMeasure n) =
        (∫ z, (ginibreSpatialCutoff n m z : ℂ) * (κ * (B z * u z)) ∂complexGaussianMeasure n) -
        ∫ z, ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) *
          (z j * H z * u z) ∂complexGaussianMeasure n := by
    let χ : Configuration n → ℂ := fun z => ginibreSpatialCutoff n m z
    have hχ : ContDiff ℝ 1 χ := Complex.ofRealCLM.contDiff.comp
      ((ginibreSpatialCutoff_smooth n m).of_le (by simp))
    have hcχ : HasCompactSupport χ :=
      (ginibreSpatialCutoff_compact n m).comp_left Complex.ofReal_zero
    have hright : (fun z => u z * ((n : ℂ) * z j * (χ z * H z) -
        dbarComponent (fun z => χ z * H z) j z)) =ᵐ[complexGaussianMeasure n]
        (fun z => χ z * (κ * (B z * u z))) -
        (fun z => ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) *
          (z j * H z * u z)) := by
      filter_upwards [hraise] with z hz
      rw [dbarComponent_mul (hχ.differentiable (by norm_num)) (hH.differentiable (by norm_num))]
      have hχd := dbarComponent_gaussianSpatialCutoff n m j z
      change dbarComponent χ j z = _ at hχd
      rw [hχd]
      dsimp only [Pi.sub_apply]
      linear_combination u z * χ z * hz
    have hi₁ : Integrable (fun z => χ z * (κ * (B z * u z))) (complexGaussianMeasure n) := by
      apply hBu.bdd_mul (c := 1) ((Complex.continuous_ofReal.comp
        (ginibreSpatialCutoff_smooth n m).continuous).aestronglyMeasurable)
      filter_upwards with z
      simpa [χ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ginibreSpatialCutoff_mem_unit n m z).1] using
        (ginibreSpatialCutoff_mem_unit n m z).2
    have hi₂ : Integrable (fun z => ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) *
        (z j * H z * u z)) (complexGaussianMeasure n) := by
      obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
      apply hEu.bdd_mul (c := M) ((Complex.continuous_ofReal.comp
        (((sobolevCutoff_smooth m).continuous_deriv (by simp)).comp
          contDiff_configurationNormSq.continuous)).aestronglyMeasurable)
      filter_upwards with z
      simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
      exact (hM m _).trans (div_le_self hM0 (by have := Nat.cast_nonneg (α := ℝ) m; linarith))
    rw [integral_congr_ae hright]
    simp only [Pi.sub_apply]
    exact integral_sub hi₁ hi₂
  have hlim := (integral_gaussianSpatialCutoff_tendsto _ hBu).sub
    (integral_gaussianSpatialCutoff_deriv_tendsto _ hEu)
  rw [gaussianHermiteCoefficient_eq_integral, ← integral_const_mul]
  simpa [H, B, κ, raiseHermiteIndex] using
    hlim.congr (fun m => (hid m).symm)

theorem gaussianWeakDbar_hermiteCoefficient {n : ℕ} (hn : 0 < n)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hu : IsGaussianWeakDbar n u D j) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn D pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq) := by
  let H := multivariateNormalized n hn pq.2 pq.1
  let B := multivariateNormalized n hn (raiseAt pq.2 j) pq.1
  let κ : ℂ := Real.sqrt (n * (pq.2 j + 1) : ℕ)
  have hH : ContDiff ℝ 1 H := contDiff_multivariateNormalized_real n hn _ _
  have hHlp : MemLp H 2 (complexGaussianMeasure n) := memLp_two_multivariateNormalized n hn _ _
  have hBlp : MemLp B 2 (complexGaussianMeasure n) := memLp_two_multivariateNormalized n hn _ _
  have hHD : Integrable (fun z => H z * D z) (complexGaussianMeasure n) :=
    hHlp.integrable_mul (Lp.memLp D)
  have hBu : Integrable (fun z => κ * (B z * u z)) (complexGaussianMeasure n) :=
    (hBlp.integrable_mul (Lp.memLp u)).const_mul κ
  have hEu : Integrable (fun z => z j * H z * u z) (complexGaussianMeasure n) :=
    (memLp_two_coordinate_mul_multivariateNormalized n hn pq.2 pq.1 j).integrable_mul (Lp.memLp u)
  have hraise : (fun z => (n : ℂ) * z j * H z - dbarComponent H j z)
      =ᵐ[complexGaussianMeasure n] (fun z => κ * B z) := by
    filter_upwards [coordinate_mul_multivariateNormalized_creation_ae n hn pq.2 pq.1 j]
      with z hz
    rw [dbarComponent_multivariateNormalized]
    dsimp [H, B, κ] at *
    rw [hz]
    ring
  have hid (m : ℕ) :
      (∫ z, (ginibreSpatialCutoff n m z : ℂ) * (H z * D z) ∂complexGaussianMeasure n) =
        (∫ z, (ginibreSpatialCutoff n m z : ℂ) * (κ * (B z * u z)) ∂complexGaussianMeasure n) -
        ∫ z, ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) *
          (z j * H z * u z) ∂complexGaussianMeasure n := by
    let χ : Configuration n → ℂ := fun z => ginibreSpatialCutoff n m z
    have hχ : ContDiff ℝ 1 χ := Complex.ofRealCLM.contDiff.comp
      ((ginibreSpatialCutoff_smooth n m).of_le (by simp))
    have hcχ : HasCompactSupport χ := (ginibreSpatialCutoff_compact n m).comp_left
        Complex.ofReal_zero
    have he := gaussianWeakDbar_integral_identity u D j hu (fun z => χ z * H z)
      (hχ.mul hH) hcχ.mul_right
    have hleft : (fun z => χ z * H z * D z) = (fun z => χ z * (H z * D z)) := by
      funext z; ring
    rw [hleft] at he
    have hright : (fun z => u z * ((n : ℂ) * z j * (χ z * H z) -
        dbarComponent (fun z => χ z * H z) j z)) =ᵐ[complexGaussianMeasure n]
        (fun z => χ z * (κ * (B z * u z))) -
        (fun z => ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) *
          (z j * H z * u z)) := by
      filter_upwards [hraise] with z hz
      rw [dbarComponent_mul (hχ.differentiable (by norm_num)) (hH.differentiable (by norm_num))]
      have hχd := dbarComponent_gaussianSpatialCutoff n m j z
      change dbarComponent χ j z = _ at hχd
      rw [hχd]
      dsimp only [Pi.sub_apply]
      linear_combination u z * χ z * hz
    rw [integral_congr_ae hright] at he
    have hi₁ : Integrable (fun z => χ z * (κ * (B z * u z))) (complexGaussianMeasure n) := by
      apply hBu.bdd_mul (c := 1) ((Complex.continuous_ofReal.comp
        (ginibreSpatialCutoff_smooth n m).continuous).aestronglyMeasurable)
      filter_upwards with z
      simpa [χ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ginibreSpatialCutoff_mem_unit n m z).1] using
        (ginibreSpatialCutoff_mem_unit n m z).2
    have hi₂ : Integrable (fun z => ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) *
        (z j * H z * u z)) (complexGaussianMeasure n) := by
      obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
      apply hEu.bdd_mul (c := M) ((Complex.continuous_ofReal.comp
        (((sobolevCutoff_smooth m).continuous_deriv (by simp)).comp
          contDiff_configurationNormSq.continuous)).aestronglyMeasurable)
      filter_upwards with z
      simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
      exact (hM m _).trans (div_le_self hM0 (by have := Nat.cast_nonneg (α := ℝ) m; linarith))
    simp only [Pi.sub_apply] at he
    rw [integral_sub hi₁ hi₂] at he
    exact he
  have hlim₁ := integral_gaussianSpatialCutoff_tendsto _ hHD
  have hlim₂ := (integral_gaussianSpatialCutoff_tendsto _ hBu).sub
    (integral_gaussianSpatialCutoff_deriv_tendsto _ hEu)
  have he : (∫ z, H z * D z ∂complexGaussianMeasure n) =
      ∫ z, κ * (B z * u z) ∂complexGaussianMeasure n := by
    have heq := tendsto_nhds_unique hlim₁ (hlim₂.congr' (Eventually.of_forall fun m => (hid
        m).symm))
    simpa using heq
  rw [gaussianHermiteCoefficient_eq_integral, gaussianHermiteCoefficient_eq_integral,
    ← integral_const_mul]
  exact he

theorem gaussianWeakDbar_of_hermiteCoefficient {n : ℕ} (hn : 0 < n)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hc : ∀ pq, gaussianHermiteCoefficient hn D pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq)) :
    IsGaussianWeakDbar n u D j := by
  have hv : Tendsto (fun s => finiteHermiteCombination n hn
      (gaussianHermiteFiniteCoefficients hn u s)) atTop (𝓝 u) := by
    simp only [gaussianHermiteFiniteCoefficients_value]
    exact (gaussianHermiteHilbertBasis n hn).hasSum_repr u
  have hd : Tendsto (fun s => finiteDbarComponentL2 n hn
      (gaussianHermiteFiniteCoefficients hn u s) j) atTop (𝓝 D) := by
    simp only [gaussianHermiteFiniteCoefficients_dbar]
    exact hasSum_gaussianHermiteFirstLoweringTerm hn u D j hc
  exact gaussianWeakDbar_of_tendsto j _ u D
    (fun s => gaussian_finiteHermite_weak_dbar n hn _ j) (hv.prodMk_nhds hd)

/-- The independently defined distributional weak graph is exactly the
 Hermite coefficient lowering graph, for arbitrary Gaussian L² inputs. -/
theorem gaussianWeakDbar_iff_hermiteCoefficient {n : ℕ} (hn : 0 < n)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) :
    IsGaussianWeakDbar n u D j ↔
      ∀ pq, gaussianHermiteCoefficient hn D pq =
        (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
          gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq) :=
  ⟨fun hu pq => gaussianWeakDbar_hermiteCoefficient hn u D j hu pq,
    gaussianWeakDbar_of_hermiteCoefficient hn u D j⟩

/-- Every arbitrary Gaussian weak derivative tuple admits simultaneous finite
 Hermite approximation in the genuine value/derivative L² topology. -/
theorem gaussianWeakDbar_finiteHermite_approximation {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u (D j) j) :
    Tendsto (fun s => finiteHermiteCombination n hn (gaussianHermiteFiniteCoefficients hn u s))
      atTop (𝓝 u) ∧
      ∀ j, Tendsto (fun s => finiteDbarComponentL2 n hn
        (gaussianHermiteFiniteCoefficients hn u s) j) atTop (𝓝 (D j)) :=
  gaussianHermiteFiniteCoefficients_tendsto hn u D
    (fun j pq => gaussianWeakDbar_hermiteCoefficient hn u (D j) j (hu j) pq)

/-- Weak Gaussian antiholomorphic derivatives are uniquely determined. -/
theorem gaussianWeakDbar_unique {n : ℕ} (hn : 0 < n)
    (u D E : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hD : IsGaussianWeakDbar n u D j) (hE : IsGaussianWeakDbar n u E j) : D = E := by
  apply (gaussianHermiteHilbertBasis n hn).repr.injective
  apply Subtype.ext
  funext pq
  exact (gaussianWeakDbar_hermiteCoefficient hn u D j hD pq).trans
    (gaussianWeakDbar_hermiteCoefficient hn u E j hE pq).symm

/-- Exact maximal derivative domain: existence of the genuine compact-test
 weak derivative is equivalent to square summability of its raising coefficients. -/
theorem gaussianWeakDbar_exists_iff_summable {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) :
    (∃ D : Lp ℂ 2 (complexGaussianMeasure n), IsGaussianWeakDbar n u D j) ↔
      Summable (fun pq : HermiteMultiIndex n =>
        ‖(Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
          gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq)‖ ^ 2) := by
  constructor
  · rintro ⟨D, hD⟩
    have hs := hasSum_norm_sq_gaussianHermiteCoefficient hn D
    exact hs.summable.congr (fun pq => by
      rw [gaussianWeakDbar_hermiteCoefficient hn u D j hD pq])
  · intro hs
    let c : lp (fun _ : HermiteMultiIndex n => ℂ) 2 :=
      ⟨fun pq => (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq),
        memℓp_gen (by simpa using hs)⟩
    let D := (gaussianHermiteHilbertBasis n hn).repr.symm c
    refine ⟨D, gaussianWeakDbar_of_hermiteCoefficient hn u D j ?_⟩
    intro pq
    change ((gaussianHermiteHilbertBasis n hn).repr D) pq = _
    rw [show (gaussianHermiteHilbertBasis n hn).repr D = c from
      (gaussianHermiteHilbertBasis n hn).repr.apply_symm_apply c]

end
end GinibrePoincare

