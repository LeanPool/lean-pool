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

public import LeanPool.GinibrePoincare.Analysis.GinibreGeneratorL2

/-! # Green identity with one compact collision-free test function
The second function is globally smooth and need not have compact support.
All density-weighted products are integrable. No boundary or analytic
certificate is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

private def densityFlux {n : ℕ} (g : Configuration n → ℝ) (v : Configuration n)
    (z : Configuration n) : ℝ := ginibreLebesgueDensityReal n z * fderiv ℝ g z v

private theorem smooth_densityFlux {n : ℕ} {g : Configuration n → ℝ}
    (hg : ContDiff ℝ ∞ g) (v : Configuration n) : ContDiff ℝ ∞ (densityFlux g v) := by
  apply (contDiff_ginibreLebesgueDensityReal n).mul
  exact (hg.contDiff_fderiv_apply (m := ∞) (by simp)).comp
    (contDiff_id.prodMk contDiff_const)

private def densityDivergence (n : ℕ) (g : Configuration n → ℝ) (z : Configuration n) : ℝ :=
  (1 / (n : ℝ)) * ∑ j : Fin n,
    (fderiv ℝ (densityFlux g (realCoordinateDirection j)) z (realCoordinateDirection j) +
      fderiv ℝ (densityFlux g (imaginaryCoordinateDirection j)) z (imaginaryCoordinateDirection j))

private theorem continuous_densityDivergence {n : ℕ} {g : Configuration n → ℝ}
    (hg : ContDiff ℝ ∞ g) : Continuous (densityDivergence n g) := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro j hj
  exact (((smooth_densityFlux hg _).continuous_fderiv (by simp)).clm_apply continuous_const).add
    (((smooth_densityFlux hg _).continuous_fderiv (by simp)).clm_apply continuous_const)

private theorem weighted_generator_ae {n : ℕ} (hn : 0 < n) {g : Configuration n → ℝ}
    (hg : ContDiff ℝ ∞ g) :
    (fun z => ginibreLebesgueDensityReal n z * ginibrePregenerator n g z) =ᵐ[volume]
      densityDivergence n g := by
  have ha : ∀ᵐ z : Configuration n ∂volume, CollisionFree z := by
    have h := configurationVolume_collisionSet hn
    have hout : ∀ᵐ z : Configuration n ∂volume, z ∉ collisionSet n := by
      rw [ae_iff]
      convert h using 1
      congr 1
      ext z
      simp
    filter_upwards [hout] with z hz
    exact (collisionFree_iff_not_mem_collisionSet z).mpr hz
  filter_upwards [ha] with z hz
  exact ginibreLebesgueDensityReal_mul_pregenerator_eq_divergence hn g hg z hz

/-- The noncompact smooth generator can be paired integrably with a core test function. -/
theorem integrable_density_core_mul_generator {n : ℕ} (hn : 0 < n)
    {f g : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) (hg : ContDiff ℝ ∞ g) :
    Integrable (fun z => ginibreLebesgueDensityReal n z * f z * ginibrePregenerator n g z) volume
      := by
  have hi : Integrable (fun z => f z * densityDivergence n g z) volume :=
    (hf.1.continuous.mul (continuous_densityDivergence hg)).integrable_of_hasCompactSupport
      (hf.2.1.mul_right)
  apply hi.congr
  filter_upwards [weighted_generator_ae hn hg] with z hz
  rw [← hz]
  ring

private def greenFlux {n : ℕ} (f g : Configuration n → ℝ) (v : Configuration n)
    (z : Configuration n) : ℝ := f z * densityFlux g v z - g z * densityFlux f v z

private theorem smooth_greenFlux {n : ℕ} {f g : Configuration n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v : Configuration n) :
    ContDiff ℝ ∞ (greenFlux f g v) :=
  (hf.mul (smooth_densityFlux hg v)).sub (hg.mul (smooth_densityFlux hf v))

private theorem compact_greenFlux {n : ℕ} {f g : Configuration n → ℝ}
    (hf : HasCompactSupport f) (v : Configuration n) : HasCompactSupport (greenFlux f g v) :=
  hf.mul_right.sub (((hf.fderiv_apply (𝕜 := ℝ) v).mul_left).mul_left)

private theorem derivative_greenFlux {n : ℕ} {f g : Configuration n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v z : Configuration n) :
    fderiv ℝ (greenFlux f g v) z v =
      f z * fderiv ℝ (densityFlux g v) z v - g z * fderiv ℝ (densityFlux f v) z v := by
  have hA := (hf.differentiable (by simp) z).hasFDerivAt.mul
    ((smooth_densityFlux hg v).differentiable (by simp) z).hasFDerivAt
  have hB := (hg.differentiable (by simp) z).hasFDerivAt.mul
    ((smooth_densityFlux hf v).differentiable (by simp) z).hasFDerivAt
  have he := congrArg (fun L => L v) (hA.sub hB).fderiv
  change fderiv ℝ (greenFlux f g v) z v = _ at he
  rw [he]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, densityFlux]
  ring

private theorem integrable_derivative_greenFlux {n : ℕ} {f g : Configuration n → ℝ}
    (hf : IsTheoremOneNineCore f) (hg : ContDiff ℝ ∞ g) (v : Configuration n) :
    Integrable (fun z => fderiv ℝ (greenFlux f g v) z v) volume :=
  (((smooth_greenFlux hf.1 hg v).continuous_fderiv (by simp)).clm_apply continuous_const)
    |>.integrable_of_hasCompactSupport ((compact_greenFlux hf.2.1 v).fderiv_apply (𝕜 := ℝ) v)

private theorem green_sum (n : ℕ) {f g : Configuration n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (z : Configuration n) :
    f z * densityDivergence n g z - g z * densityDivergence n f z =
      (1 / (n : ℝ)) * ∑ j : Fin n,
        (fderiv ℝ (greenFlux f g (realCoordinateDirection j)) z (realCoordinateDirection j) +
          fderiv ℝ (greenFlux f g (imaginaryCoordinateDirection j)) z
            (imaginaryCoordinateDirection j)) := by
  simp_rw [derivative_greenFlux hf hg]
  unfold densityDivergence
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  ring

/-- The concrete weighted Green identity, with a globally smooth second function. -/
theorem ginibre_density_mixed_green_identity {n : ℕ} (hn : 0 < n)
    {f g : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) (hg : ContDiff ℝ ∞ g) :
    (∫ z, ginibreLebesgueDensityReal n z * f z * ginibrePregenerator n g z) =
      ∫ z, ginibreLebesgueDensityReal n z * g z * ginibrePregenerator n f z := by
  have hir := integrable_density_core_mul_generator hn hf hg
  have hil : Integrable (fun z => ginibreLebesgueDensityReal n z * g z * ginibrePregenerator n f
    z) volume :=
    (((contDiff_ginibreLebesgueDensityReal n).continuous.mul hg.continuous).mul
      (continuous_ginibrePregenerator_of_core hf)).integrable_of_hasCompactSupport
        ((hasCompactSupport_ginibrePregenerator hf.2.1).mul_left)
  have hzero : (∫ z, ginibreLebesgueDensityReal n z * f z * ginibrePregenerator n g z -
      ginibreLebesgueDensityReal n z * g z * ginibrePregenerator n f z) = 0 := by
    calc
      _ = ∫ z, f z * densityDivergence n g z - g z * densityDivergence n f z := by
        apply integral_congr_ae
        filter_upwards [weighted_generator_ae hn hg, weighted_generator_ae hn hf.1] with z hg hf
        rw [← hg, ← hf]; ring
      _ = (1 / (n : ℝ)) * ∫ z, ∑ j : Fin n,
          (fderiv ℝ (greenFlux f g (realCoordinateDirection j)) z (realCoordinateDirection j) +
            fderiv ℝ (greenFlux f g (imaginaryCoordinateDirection j)) z
              (imaginaryCoordinateDirection j)) := by
        simp_rw [green_sum n hf.1 hg]
        rw [integral_const_mul]
      _ = 0 := by
        rw [integral_finsetSum]
        · have hr (j : Fin n) := integral_fderiv_configuration_real_eq_zero
            (greenFlux f g (realCoordinateDirection j))
            ((smooth_greenFlux hf.1 hg _).of_le (by simp)) (compact_greenFlux hf.2.1 _) j
          have hi (j : Fin n) := integral_fderiv_configuration_imag_eq_zero
            (greenFlux f g (imaginaryCoordinateDirection j))
            ((smooth_greenFlux hf.1 hg _).of_le (by simp)) (compact_greenFlux hf.2.1 _) j
          simp_rw [integral_add (integrable_derivative_greenFlux hf hg _)
            (integrable_derivative_greenFlux hf hg _),
            hr, hi, add_zero]
          simp
        · intro j hj
          exact (integrable_derivative_greenFlux hf hg _).add (integrable_derivative_greenFlux hf
            hg _)
  rw [integral_sub hir hil] at hzero
  exact sub_eq_zero.mp hzero

/-- Full real Ginibre Green identity: the polynomial need not lie in the compact core. -/
theorem ginibre_mixed_green_identity {n : ℕ} (hn : 0 < n)
    {f g : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) (hg : ContDiff ℝ ∞ g) :
    (∫ z, f z * ginibrePregenerator n g z ∂ginibreMeasure n) =
      ∫ z, g z * ginibrePregenerator n f z ∂ginibreMeasure n := by
  rw [integral_ginibreMeasure_eq_density_volume hn, integral_ginibreMeasure_eq_density_volume hn]
  congr 1
  simp_rw [← mul_assoc]
  exact ginibre_density_mixed_green_identity hn hf hg

end
end GinibrePoincare
