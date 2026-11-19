/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare.

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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarParseval
public import LeanPool.GinibrePoincare.Analysis.GinibreComplexL2

/-! # The weak Wirtinger derivative and its Vandermonde transform -/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped ComplexConjugate ContDiff BigOperators

/-- Actual complex coordinate `Wirtinger derivative` assembled from the full weak real gradient. -/
def ginibreFullWeakDbar (n : ℕ) (j : Fin n) :
    GinibreFullGradientL2 n →L[ℝ] GinibreFullComplexL2 n :=
  (1 / 2 : ℝ) • ((ginibreFullComplexOfReal n).comp
    ((PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) (j, 0) : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ]
      ℝ).compLpL 2 (ginibreMeasure n)) +
    Complex.I • (ginibreFullComplexOfReal n).comp
    ((PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) (j, 1) : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ]
      ℝ).compLpL 2 (ginibreMeasure n)))

/-- Bounded full-domain Gaussian derivative transform; no pointwise smoothness
of the weak input is used in this construction. -/
def ginibreFullTransformedDbar (n : ℕ) (hn : 0 < n) (j : Fin n) :
    GinibreFullGradientL2 n →L[ℝ] Lp ℂ 2 (complexGaussianMeasure n) :=
  ((normalizedVandermondeL2 n hn).toContinuousLinearMap.restrictScalars ℝ).comp
    (ginibreFullWeakDbar n j)

theorem ginibreFullWeakDbar_ae (n : ℕ) (j : Fin n) (g : GinibreFullGradientL2 n) :
    (ginibreFullWeakDbar n j g : Configuration n → ℂ) =ᵐ[ginibreMeasure n]
      fun z => (1 / 2 : ℂ) * ((g z (j, 0) : ℂ) + Complex.I * (g z (j, 1) : ℂ)) := by
  let r := (PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) (j, 0) : EuclideanSpace ℝ (Fin n × Fin 2)
    →L[ℝ] ℝ).compLpL 2 (ginibreMeasure n) g
  let i := (PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) (j, 1) : EuclideanSpace ℝ (Fin n × Fin 2)
    →L[ℝ] ℝ).compLpL 2 (ginibreMeasure n) g
  let R := ginibreFullComplexOfReal n r
  let I := ginibreFullComplexOfReal n i
  simp only [ginibreFullWeakDbar, smul_apply,
    add_apply, ContinuousLinearMap.comp_apply]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (R + Complex.I • I),
    Lp.coeFn_add R (Complex.I • I), Lp.coeFn_smul Complex.I I,
    ginibreFullComplexOfReal_ae n r, ginibreFullComplexOfReal_ae n i,
    (PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) (j, 0) : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ]
      ℝ).coeFn_compLpL g,
    (PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) (j, 1) : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ]
      ℝ).coeFn_compLpL g]
    with z hs ha hi hr he hgr hgi
  rw [hs]
  simp only [Pi.smul_apply]
  rw [ha]
  simp only [Pi.add_apply]
  rw [hi]
  simp only [Pi.smul_apply]
  rw [hr, he, hgr, hgi]
  simp only [PiLp.proj_apply, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring

/-- Concrete representative of the normalized Vandermonde isometry. -/
theorem ginibreFullNormalizedVandermonde_ae (n : ℕ) (hn : 0 < n)
    (u : GinibreFullComplexL2 n) :
    (normalizedVandermondeL2 n hn u : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      fun z => normalizedVandermondeMultiplier n z * u z := by
  exact normalizedVandermondeL2_coeFn_public n hn u

/-- Actual transformed weak derivative has the expected representative. -/
theorem ginibreFullTransformedDbar_ae (n : ℕ) (hn : 0 < n) (j : Fin n)
    (g : GinibreFullGradientL2 n) :
    (ginibreFullTransformedDbar n hn j g : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      fun z => normalizedVandermondeMultiplier n z *
        ((1 / 2 : ℂ) * ((g z (j, 0) : ℂ) + Complex.I * (g z (j, 1) : ℂ))) := by
  have hv := ginibreFullNormalizedVandermonde_ae n hn (ginibreFullWeakDbar n j g)
  have hg := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq (ginibreFullWeakDbar_ae n j g)
  filter_upwards [hv, hg] with z hz hg
  exact hz.trans (congrArg (fun a : ℂ => normalizedVandermondeMultiplier n z * a) hg)

/-- The full derivative transform agrees with the genuine smooth Gaussian
`Wirtinger derivative` on every compactly supported smooth representative. -/
theorem ginibreFullTransformedDbar_smooth {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (g : GinibreFullGradientL2 n)
    (hg : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
      ginibreEuclideanGradient f) (j : Fin n) :
    ginibreFullTransformedDbar n hn j g =
      smoothDbarComponentL2
        (normalizedVandermondeTransform n (fun z => (f z : ℂ)))
        (contDiff_normalizedVandermonde_ofReal hf |>.of_le (by norm_num))
        (hasCompactSupport_normalizedVandermonde_ofReal hc) j := by
  apply Lp.ext
  have hga := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq hg
  filter_upwards [ginibreFullTransformedDbar_ae n hn j g, hga,
    smoothDbarComponentL2_coeFn
      (normalizedVandermondeTransform n (fun z => (f z : ℂ)))
      (contDiff_normalizedVandermonde_ofReal hf |>.of_le (by norm_num))
      (hasCompactSupport_normalizedVandermonde_ofReal hc) j] with z hd hg hs
  rw [hd, hs, hg]
  have hdiff : Differentiable ℝ (fun z => (f z : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp (hf.differentiable (by norm_num))
  rw [dbarComponent_normalizedVandermondeTransform hdiff,
    dbarComponent_ofReal (hf.differentiable (by norm_num))]
  simp only [ginibreEuclideanGradient_coordinate, ginibreCoordinateDirection]
  simp [normalizedVandermondeMultiplier]

/-- Actual full value transform agrees with its smooth compact Gaussian class. -/
theorem ginibreFullTransformedValue_smooth {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : GinibreFullValueL2 n)
    (hu : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f) :
    normalizedVandermondeL2 n hn (ginibreFullComplexOfReal n u) =
      smoothCompactL2 (normalizedVandermondeTransform n (fun z => (f z : ℂ)))
        (contDiff_normalizedVandermonde_ofReal hf |>.of_le (by norm_num))
        (hasCompactSupport_normalizedVandermonde_ofReal hc) := by
  apply Lp.ext
  have hu' := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq hu
  have hr := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq (ginibreFullComplexOfReal_ae n u)
  filter_upwards [normalizedVandermondeL2_coeFn_public n hn (ginibreFullComplexOfReal n u),
    hu', hr, smoothCompactL2_coeFn
      (normalizedVandermondeTransform n (fun z => (f z : ℂ)))
      (contDiff_normalizedVandermonde_ofReal hf |>.of_le (by norm_num))
      (hasCompactSupport_normalizedVandermonde_ofReal hc)] with z hv hu hr hs
  rw [hv, hs, hr, hu, normalizedVandermondeTransform_apply]
  rfl

/-- Exact Hermite lowering equation for every actual compact smooth pair. -/
theorem ginibreFullTransformedDbar_smooth_coefficient {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hg : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
      ginibreEuclideanGradient f) (j : Fin n) (pq : ComplexHermite.HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (ginibreFullTransformedDbar n hn j g) pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn
          (normalizedVandermondeL2 n hn (ginibreFullComplexOfReal n u))
          (ComplexHermite.raiseHermiteIndex j pq) := by
  rw [ginibreFullTransformedDbar_smooth hn f hf hc g hg j,
    ginibreFullTransformedValue_smooth hn f hf hc u hu]
  exact gaussianHermiteCoefficient_smoothDbarComponentL2_raise hn _ _ _ j pq

/-- Exact norm of the full weak derivative transform. -/
theorem ginibreFullTransformedDbar_norm_sum {n : ℕ} (hn : 0 < n)
    (g : GinibreFullGradientL2 n) :
    (∑ j : Fin n, ‖ginibreFullTransformedDbar n hn j g‖ ^ 2) = (1 / 4 : ℝ) * ‖g‖ ^ 2 := by
  have hnD (j : Fin n) : ‖ginibreFullTransformedDbar n hn j g‖ =
      ‖ginibreFullWeakDbar n j g‖ := (normalizedVandermondeL2 n hn).norm_map _
  simp_rw [hnD, ← integral_norm_sq_eq_L2_norm_sq (ginibreMeasure n)]
  rw [← integral_finsetSum Finset.univ (fun j _ =>
    (Lp.memLp (ginibreFullWeakDbar n j g)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)),
    ← integral_const_mul]
  apply integral_congr_ae
  have hD : ∀ᵐ z ∂ginibreMeasure n, ∀ j, (ginibreFullWeakDbar n j g) z =
      (1 / 2 : ℂ) * ((g z (j, 0) : ℂ) + Complex.I * (g z (j, 1) : ℂ)) :=
    ae_all_iff.mpr (ginibreFullWeakDbar_ae n · g)
  filter_upwards [hD] with z hz
  have hc (j : Fin n) : ‖(ginibreFullWeakDbar n j g) z‖ ^ 2 =
      (1 / 4 : ℝ) * ((g z (j, 0)) ^ 2 + (g z (j, 1)) ^ 2) := by
    rw [hz j, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    ring
  simp_rw [hc]
  rw [← Finset.mul_sum, PiLp.norm_sq_eq_of_L2]
  congr 1
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

end GinibrePoincare
