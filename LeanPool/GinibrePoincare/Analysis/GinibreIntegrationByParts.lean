/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreIntegrationByParts.lean.
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

public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Integrability preliminaries for Ginibre integration by parts -/


@[expose] public section


open MeasureTheory
open scoped BigOperators ContDiff ComplexConjugate

namespace GinibrePoincare

noncomputable section


/-- The integral over the real line of the derivative of a compactly
supported `C¹` function vanishes. -/
theorem integral_deriv_eq_zero_of_contDiff_hasCompactSupport
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∫ x, deriv g x = 0 := by
  have hi : Integrable (deriv g) :=
    (hg.continuous_deriv (by simp)).integrable_of_hasCompactSupport hgc.deriv
  rw [← integral_add_compl (μ := volume) measurableSet_Iic hi]
  rw [show (Set.Iic (0 : ℝ))ᶜ = Set.Ioi 0 by ext x; simp]
  rw [hgc.integral_Iic_deriv_eq hg 0, hgc.integral_Ioi_deriv_eq hg 0]
  ring

private theorem hasCompactSupport_complexRealSlice {H : ℂ → ℝ}
    (hH : HasCompactSupport H) (y : ℝ) :
    HasCompactSupport (fun x : ℝ => H ⟨x, y⟩) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hH.image (Complex.reCLM.continuous))
  intro x hx
  exact ⟨⟨x, y⟩, subset_tsupport _ hx, rfl⟩

private theorem deriv_complexRealSlice_real {H : ℂ → ℝ}
    (hH : ContDiff ℝ 1 H) (y x : ℝ) :
    deriv (fun r : ℝ => H ⟨r, y⟩) x =
      fderiv ℝ H ⟨x, y⟩ (1 : ℂ) := by
  apply HasDerivAt.deriv
  have hfun : (fun r : ℝ => H ⟨r, y⟩) =
      H ∘ fun r : ℝ => (r : ℂ) + (y : ℂ) * Complex.I := by
    funext r
    congr 1
    apply Complex.ext <;> simp
  rw [hfun]
  have hi : HasDerivAt (fun r : ℝ => (r : ℂ) + (y : ℂ) * Complex.I)
      (1 : ℂ) x := by
    simpa using (Complex.ofRealCLM.hasFDerivAt.hasDerivAt.add_const
      ((y : ℂ) * Complex.I))
  have heq : (x : ℂ) + (y : ℂ) * Complex.I = ⟨x, y⟩ := by
    apply Complex.ext <;> simp
  rw [← heq]
  change HasDerivAt (H ∘ fun r : ℝ => (r : ℂ) + (y : ℂ) * Complex.I) _ x
  exact (hH.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt x hi

/-- A compactly supported smooth scalar field on the complex plane has zero
integral of its real directional derivative. -/
theorem integral_fderiv_complex_real_eq_zero (H : ℂ → ℝ)
    (hH : ContDiff ℝ 1 H) (hHc : HasCompactSupport H) :
    ∫ z : ℂ, fderiv ℝ H z (1 : ℂ) = 0 := by
  have hi : Integrable (fun z : ℂ => fderiv ℝ H z (1 : ℂ)) :=
    ((hH.continuous_fderiv (by simp)).clm_apply continuous_const)
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hHc (1 : ℂ))
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integral_comp']
  have hip : Integrable (fun p : ℝ × ℝ =>
      fderiv ℝ H (Complex.measurableEquivRealProd.symm p) (1 : ℂ)) := by
    rw [← Complex.volume_preserving_equiv_real_prod.symm.map_eq] at hi
    exact (integrable_map_equiv Complex.measurableEquivRealProd.symm _).mp hi
  change (∫ p : ℝ × ℝ,
    fderiv ℝ H (Complex.measurableEquivRealProd.symm p) (1 : ℂ)
      ∂volume.prod volume) = 0
  rw [integral_prod_symm _ hip]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  simp only [Complex.measurableEquivRealProd_symm_apply]
  change (∫ x : ℝ, fderiv ℝ H ⟨x, y⟩ 1) = 0
  rw [show (fun x : ℝ => fderiv ℝ H ⟨x, y⟩ 1) =
      fun x => deriv (fun r : ℝ => H ⟨r, y⟩) x by
    funext x
    exact (deriv_complexRealSlice_real hH y x).symm]
  exact integral_deriv_eq_zero_of_contDiff_hasCompactSupport _
    (by
      rw [show (fun r : ℝ => H ⟨r, y⟩) =
          fun r : ℝ => H ((r : ℂ) + (y : ℂ) * Complex.I) by
        funext r; congr 1; apply Complex.ext <;> simp]
      apply hH.comp
      exact Complex.ofRealCLM.contDiff.add
        (contDiff_const.mul contDiff_const))
    (hasCompactSupport_complexRealSlice hHc y)

/-- Fubini splitting of a finite product measure at an arbitrary coordinate. -/
theorem integral_configuration_finSucc_split_measure {k : ℕ}
    (μ : Measure ℂ) [SigmaFinite μ] (j : Fin (k + 1))
    {H : Configuration (k + 1) → ℝ}
    (hH : Integrable H (Measure.pi fun _ : Fin (k + 1) => μ)) :
    (∫ z, H z ∂(Measure.pi fun _ : Fin (k + 1) => μ)) =
      ∫ r : Fin k → ℂ, ∫ w : ℂ,
        H ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (k + 1) => ℂ) j).symm (w, r))
        ∂μ ∂(Measure.pi fun _ : Fin k => μ) := by
  let ν : Fin (k + 1) → Measure ℂ := fun _ => μ
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (k + 1) => ℂ) j
  have he : MeasurePreserving e (Measure.pi ν)
      ((ν j).prod (Measure.pi fun i : Fin k => ν (j.succAbove i))) :=
    measurePreserving_piFinSuccAbove ν j
  have hprod : Integrable (H ∘ e.symm)
      ((ν j).prod (Measure.pi fun i : Fin k => ν (j.succAbove i))) :=
    he.symm.integrable_comp_of_integrable hH
  calc
    _ = ∫ p : ℂ × (Fin k → ℂ), H (e.symm p)
        ∂((ν j).prod (Measure.pi fun i : Fin k => ν (j.succAbove i))) :=
      (he.symm.integral_comp' H).symm
    _ = ∫ r : Fin k → ℂ, ∫ w : ℂ, H (e.symm (w, r))
        ∂(ν j) ∂(Measure.pi fun i : Fin k => ν (j.succAbove i)) :=
      integral_prod_symm _ hprod
    _ = _ := by simp only [ν, e]

private theorem fderiv_comp_configurationCoordinateSlice_apply_real {m : ℕ}
    {F : Configuration m → ℝ} (hF : ContDiff ℝ 1 F)
    (r : Configuration m) (j : Fin m) (w v : ℂ) :
    fderiv ℝ (fun u => F (configurationCoordinateSlice r j u)) w v =
      fderiv ℝ F (configurationCoordinateSlice r j w) (coordinateDirection j v) := by
  change fderiv ℝ (F ∘ configurationCoordinateSlice r j) w v = _
  have hout := (hF.differentiable (by simp)
    (configurationCoordinateSlice r j w)).hasFDerivAt
  have hcomp := HasFDerivAt.comp w hout
    (hasFDerivAt_configurationCoordinateSlice r j w)
  have hv := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) hcomp.fderiv
  rw [show coordinateDirection j v = Pi.single j v by
    funext i; simp [coordinateDirection, Pi.single_apply]]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply] using hv

private theorem hasCompactSupport_comp_configurationCoordinateSlice_real {m : ℕ}
    {F : Configuration m → ℝ} (hF : HasCompactSupport F)
    (r : Configuration m) (j : Fin m) :
    HasCompactSupport (fun w => F (configurationCoordinateSlice r j w)) := by
  apply HasCompactSupport.intro
    ((isometry_configurationCoordinateSlice r j).isClosedEmbedding.isCompact_preimage hF)
  intro w hw
  by_contra hne
  exact hw (subset_closure hne)

/-- A compactly supported `C¹` function has zero integral of each real
configuration-coordinate derivative. -/
theorem integral_fderiv_configuration_real_eq_zero {n : ℕ}
    (Φ : Configuration n → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (hΦc : HasCompactSupport Φ) (j : Fin n) :
    ∫ z, fderiv ℝ Φ z (realCoordinateDirection j) = 0 := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ k =>
    have hi : Integrable (fun z => fderiv ℝ Φ z (realCoordinateDirection j)) :=
      ((hΦ.continuous_fderiv (by simp)).clm_apply continuous_const)
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hΦc _)
    change (∫ z, fderiv ℝ Φ z (realCoordinateDirection j)
      ∂(Measure.pi fun _ : Fin (k + 1) => (volume : Measure ℂ))) = 0
    rw [integral_configuration_finSucc_split_measure volume j hi]
    apply integral_eq_zero_of_ae
    filter_upwards with r
    let b : Configuration (k + 1) :=
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (k + 1) => ℂ) j).symm (0, r)
    rw [show (fun w => fderiv ℝ Φ
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) j).symm (w, r))
          (realCoordinateDirection j)) =
        fun w => fderiv ℝ (fun u => Φ (configurationCoordinateSlice b j u)) w 1 by
      funext w
      rw [piFinSuccAbove_symm_eq_coordinateSlice j]
      exact (fderiv_comp_configurationCoordinateSlice_apply_real hΦ b j w 1).symm]
    exact integral_fderiv_complex_real_eq_zero _
      (hΦ.comp (contDiff_configurationCoordinateSlice b j))
      (hasCompactSupport_comp_configurationCoordinateSlice_real hΦc b j)

private theorem hasCompactSupport_complexImagSlice_real {H : ℂ → ℝ}
    (hH : HasCompactSupport H) (x : ℝ) :
    HasCompactSupport (fun y : ℝ => H ⟨x, y⟩) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hH.image Complex.imCLM.continuous)
  intro y hy
  exact ⟨⟨x, y⟩, subset_tsupport _ hy, rfl⟩

private theorem deriv_complexImagSlice_real {H : ℂ → ℝ}
    (hH : ContDiff ℝ 1 H) (x y : ℝ) :
    deriv (fun r : ℝ => H ⟨x, r⟩) y = fderiv ℝ H ⟨x, y⟩ Complex.I := by
  apply HasDerivAt.deriv
  have hfun : (fun r : ℝ => H ⟨x, r⟩) =
      H ∘ fun r : ℝ => (x : ℂ) + (r : ℂ) * Complex.I := by
    funext r; congr 1; apply Complex.ext <;> simp
  rw [hfun]
  have hi : HasDerivAt (fun r : ℝ => (x : ℂ) + (r : ℂ) * Complex.I)
      Complex.I y := by
    simpa using ((Complex.ofRealCLM.hasFDerivAt.hasDerivAt.mul_const
      Complex.I).const_add (x : ℂ))
  have heq : (x : ℂ) + (y : ℂ) * Complex.I = ⟨x, y⟩ := by
    apply Complex.ext <;> simp
  rw [← heq]
  exact (hH.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt y hi

theorem integral_fderiv_complex_imag_eq_zero (H : ℂ → ℝ)
    (hH : ContDiff ℝ 1 H) (hHc : HasCompactSupport H) :
    ∫ z : ℂ, fderiv ℝ H z Complex.I = 0 := by
  have hi : Integrable (fun z : ℂ => fderiv ℝ H z Complex.I) :=
    ((hH.continuous_fderiv (by simp)).clm_apply continuous_const)
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hHc Complex.I)
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integral_comp']
  rw [← Complex.volume_preserving_equiv_real_prod.symm.map_eq] at hi
  have hip : Integrable (fun p : ℝ × ℝ =>
      fderiv ℝ H (Complex.measurableEquivRealProd.symm p) Complex.I)
      (volume.prod volume) :=
    (integrable_map_equiv Complex.measurableEquivRealProd.symm _).mp hi
  change (∫ p : ℝ × ℝ,
    fderiv ℝ H (Complex.measurableEquivRealProd.symm p) Complex.I
      ∂volume.prod volume) = 0
  rw [integral_prod _ hip]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  simp only [Complex.measurableEquivRealProd_symm_apply]
  change (∫ y : ℝ, fderiv ℝ H ⟨x, y⟩ Complex.I) = 0
  rw [show (fun y : ℝ => fderiv ℝ H ⟨x, y⟩ Complex.I) =
      fun y => deriv (fun r : ℝ => H ⟨x, r⟩) y by
    funext y; exact (deriv_complexImagSlice_real hH x y).symm]
  exact integral_deriv_eq_zero_of_contDiff_hasCompactSupport _
    (by
      rw [show (fun r : ℝ => H ⟨x, r⟩) =
          fun r : ℝ => H ((x : ℂ) + (r : ℂ) * Complex.I) by
        funext r; congr 1; apply Complex.ext <;> simp]
      exact hH.comp (contDiff_const.add
        (Complex.ofRealCLM.contDiff.mul contDiff_const)))
    (hasCompactSupport_complexImagSlice_real hHc x)

theorem integral_fderiv_configuration_imag_eq_zero {n : ℕ}
    (Φ : Configuration n → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (hΦc : HasCompactSupport Φ) (j : Fin n) :
    ∫ z, fderiv ℝ Φ z (imaginaryCoordinateDirection j) = 0 := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ k =>
    have hi : Integrable (fun z => fderiv ℝ Φ z (imaginaryCoordinateDirection j)) :=
      ((hΦ.continuous_fderiv (by simp)).clm_apply continuous_const)
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hΦc _)
    change (∫ z, fderiv ℝ Φ z (imaginaryCoordinateDirection j)
      ∂(Measure.pi fun _ : Fin (k + 1) => (volume : Measure ℂ))) = 0
    rw [integral_configuration_finSucc_split_measure volume j hi]
    apply integral_eq_zero_of_ae
    filter_upwards with r
    let b : Configuration (k + 1) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) j).symm (0, r)
    rw [show (fun w => fderiv ℝ Φ
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) j).symm (w, r))
          (imaginaryCoordinateDirection j)) =
        fun w => fderiv ℝ (fun u => Φ (configurationCoordinateSlice b j u)) w Complex.I by
      funext w
      rw [piFinSuccAbove_symm_eq_coordinateSlice j]
      exact (fderiv_comp_configurationCoordinateSlice_apply_real hΦ b j w Complex.I).symm]
    exact integral_fderiv_complex_imag_eq_zero _
      (hΦ.comp (contDiff_configurationCoordinateSlice b j))
      (hasCompactSupport_comp_configurationCoordinateSlice_real hΦc b j)

/-- The ordinary real density whose `ENNReal.ofReal` is the product of the
Vandermonde and explicit complex-Gaussian densities. -/
def ginibreLebesgueDensityReal (n : ℕ) (z : Configuration n) : ℝ :=
  (((n : ℝ) / Real.pi) ^ n) * vandermondeWeight z * gaussianWeight n z

/-- The real Ginibre Lebesgue density is nonnegative. -/
theorem ginibreLebesgueDensityReal_nonneg (n : ℕ) (z : Configuration n) :
    0 ≤ ginibreLebesgueDensityReal n z := by
  unfold ginibreLebesgueDensityReal
  exact mul_nonneg (mul_nonneg (pow_nonneg (div_nonneg (Nat.cast_nonneg n)
    Real.pi_pos.le) _) (vandermondeWeight_nonneg z)) (gaussianWeight_nonneg n z)

/-- The two extended nonnegative density factors multiply to the `ofReal`
of the ordinary real density. -/
theorem vandermondeDensity_mul_complexGaussianDensity (n : ℕ)
    (z : Configuration n) :
    vandermondeDensity z * complexGaussianDensity n z =
      ENNReal.ofReal (ginibreLebesgueDensityReal n z) := by
  unfold vandermondeDensity complexGaussianDensity ginibreLebesgueDensityReal
  rw [← ENNReal.ofReal_mul (vandermondeWeight_nonneg z)]
  congr 1
  ring

/-- Integration against normalized Ginibre measure as ordinary Lebesgue
integration against the explicit real density. -/
theorem integral_ginibreMeasure_eq_density_volume {n : ℕ} (hn : 0 < n)
    (h : Configuration n → ℝ) :
    ∫ z, h z ∂ginibreMeasure n =
      (ginibreNormalizingMass n).toReal⁻¹ *
        ∫ z, ginibreLebesgueDensityReal n z * h z := by
  rw [integral_ginibreMeasure, complexGaussianDensityIdentification n hn]
  unfold complexGaussianDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_complexGaussianDensity n)
    (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
  simp_rw [complexGaussianDensity,
    ENNReal.toReal_ofReal (mul_nonneg
      (pow_nonneg (div_nonneg (Nat.cast_nonneg n) Real.pi_pos.le) _)
      (gaussianWeight_nonneg n _)), smul_eq_mul]
  congr 2
  funext z
  unfold ginibreLebesgueDensityReal
  ring

/-- The ordinary Ginibre density is smooth on the whole configuration
space (and hence, in particular, on the collision-free locus). -/
theorem contDiff_ginibreLebesgueDensityReal (n : ℕ) :
    ContDiff ℝ ∞ (ginibreLebesgueDensityReal n) := by
  unfold ginibreLebesgueDensityReal vandermondeWeight gaussianWeight
  have hV : ContDiff ℝ ∞ (fun z : Configuration n => vandermonde z) :=
    contDiff_vandermonde n
  have hVre : ContDiff ℝ ∞ (fun z : Configuration n => (vandermonde z).re) :=
    Complex.reCLM.contDiff.comp hV
  have hVim : ContDiff ℝ ∞ (fun z : Configuration n => (vandermonde z).im) :=
    Complex.imCLM.contDiff.comp hV
  simp_rw [Complex.normSq_apply]
  have hnorm : ContDiff ℝ ∞ (configurationNormSq : Configuration n → ℝ) := by
    unfold configurationNormSq
    simp_rw [Complex.normSq_apply]
    apply ContDiff.sum
    intro i hi
    have hp : ContDiff ℝ ∞ (fun z : Configuration n => z i) :=
      (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).contDiff
    exact ((Complex.reCLM.contDiff.comp hp).mul (Complex.reCLM.contDiff.comp hp)).add
      ((Complex.imCLM.contDiff.comp hp).mul (Complex.imCLM.contDiff.comp hp))
  have hexp : ContDiff ℝ ∞ (fun z : Configuration n =>
      Real.exp (-(n : ℝ) * configurationNormSq z)) := by
    simpa only [neg_mul] using
      (((contDiff_const : ContDiff ℝ ∞
        (fun _ : Configuration n => (n : ℝ))).mul hnorm).neg.exp)
  exact (contDiff_const.mul ((hVre.mul hVre).add (hVim.mul hVim))).mul hexp

/-- Smoothness restricted to the collision-free open set. -/
theorem contDiffOn_ginibreLebesgueDensityReal_collisionFree (n : ℕ) :
    ContDiffOn ℝ ∞ (ginibreLebesgueDensityReal n) (collisionSet n)ᶜ :=
  (contDiff_ginibreLebesgueDensityReal n).contDiffOn

/-- Logarithmic derivative of a finite nonvanishing product.  This is the
calculus lemma used for the collision-free Vandermonde product. -/
theorem fderiv_finsetProd_apply_eq_prod_mul_sum_div
    {ι : Type*} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : Finset ι) (g : ι → E → ℂ) (x v : E)
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) x)
    (hne : ∀ i ∈ s, g i x ≠ 0) :
    fderiv ℝ (fun y => ∏ i ∈ s, g i y) x v =
      (∏ i ∈ s, g i x) *
        ∑ i ∈ s, fderiv ℝ (g i) x v / g i x := by
  classical
  rw [fderiv_finsetProd hg]
  simp only [sum_apply, smul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_eq_mul]
  field_simp [hne i hi]
  calc
    _ = (fderiv ℝ (g i) x) v *
        ((∏ j ∈ s.erase i, g j x) * g i x) := by ring
    _ = _ := by rw [Finset.prod_erase_mul s (fun j => g j x) hi]

/-- Every factor in the ordered Vandermonde product is nonzero at a
collision-free configuration. -/
theorem vandermondeFactor_ne_zero_of_collisionFree {n : ℕ}
    {z : Configuration n} (hz : CollisionFree z) {i k : Fin n} (hik : i < k) :
    z k - z i ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  exact (ne_of_gt hik) (hz h)

/-- A single ordered factor in the Vandermonde product. -/
def vandermondeFactor {n : ℕ} (i k : Fin n) (z : Configuration n) : ℂ :=
  z k - z i

/-- Strictly ordered particle pairs indexing the Vandermonde factors. -/
abbrev VandermondePair (n : ℕ) := {ik : Fin n × Fin n // ik.1 < ik.2}

/-- The Vandermonde product flattened over its subtype of strictly ordered
pairs. -/
theorem vandermonde_eq_prod_pair {n : ℕ} (z : Configuration n) :
    vandermonde z =
      ∏ ik : VandermondePair n, vandermondeFactor ik.1.1 ik.1.2 z := by
  rw [vandermonde_eq_product]
  rw [← Finset.prod_subtype
    (Finset.univ.filter (fun ik : Fin n × Fin n => ik.1 < ik.2)) (by simp)
    (fun ik => vandermondeFactor ik.1 ik.2 z)]
  rw [Finset.prod_filter]
  rw [Fintype.prod_prod_type]
  simp only [vandermondeFactor]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.prod_filter]
  apply Finset.prod_congr
  · ext j
    simp
  · intro j hj
    rfl

/-- Exact real Fréchet derivative of one Vandermonde factor in a coordinate
direction. -/
theorem fderiv_vandermondeFactor_apply_coordinateDirection {n : ℕ}
    (i k j : Fin n) (hik : i ≠ k) (w : ℂ) (z : Configuration n) :
    fderiv ℝ (vandermondeFactor i k) z (coordinateDirection j w) =
      if j = k then w else if j = i then -w else 0 := by
  let L : Configuration n →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj k : Configuration n →L[ℝ] ℂ) -
      (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ)
  have hfun : vandermondeFactor i k = L := by
    funext x
    rfl
  rw [hfun, L.fderiv]
  simp only [L, sub_apply]
  by_cases hjk : j = k
  · simp [coordinateDirection, hjk, hik]
  · by_cases hji : j = i
    · simp [coordinateDirection, hji, hik, eq_comm]
    · have hkj : k ≠ j := Ne.symm hjk
      have hij : i ≠ j := Ne.symm hji
      simp [coordinateDirection, hjk, hji, hkj, hij]

/-- Direct specialization of the finite-product logarithmic derivative to
the subtype of ordered Vandermonde pairs. -/
theorem fderiv_vandermonde_apply_coordinateDirection_eq_pairSum {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) (w : ℂ) :
    fderiv ℝ vandermonde z (coordinateDirection j w) = vandermonde z *
      ∑ ik : VandermondePair n,
        (if j = ik.1.2 then w else if j = ik.1.1 then -w else 0) /
          (z ik.1.2 - z ik.1.1) := by
  rw [show vandermonde = fun y =>
      ∏ ik : VandermondePair n, vandermondeFactor ik.1.1 ik.1.2 y by
    funext y
    exact vandermonde_eq_prod_pair y]
  rw [fderiv_finsetProd_apply_eq_prod_mul_sum_div Finset.univ
    (fun ik : VandermondePair n => vandermondeFactor ik.1.1 ik.1.2)
    z (coordinateDirection j w)]
  · congr 1
    apply Finset.sum_congr rfl
    intro ik hik
    rw [fderiv_vandermondeFactor_apply_coordinateDirection _ _ _
      (ne_of_lt ik.2) w z]
    rfl
  · intro ik hik
    let L : Configuration n →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj ik.1.2 : Configuration n →L[ℝ] ℂ) -
        (ContinuousLinearMap.proj ik.1.1 : Configuration n →L[ℝ] ℂ)
    exact L.differentiable.differentiableAt
  · intro ik hik
    exact vandermondeFactor_ne_zero_of_collisionFree hz ik.2

/-- Ordered pairs incident to a fixed particle. -/
abbrev IncidentVandermondePair {n : ℕ} (j : Fin n) :=
  {ik : VandermondePair n // j = ik.1.1 ∨ j = ik.1.2}

/-- The unique ordered pair associated with a particle distinct from `j`. -/
def incidentPair {n : ℕ} (j : Fin n) (k : {k : Fin n // k ≠ j}) :
    IncidentVandermondePair j := by
  classical
  by_cases h : k.1 < j
  · exact ⟨⟨(k.1, j), h⟩, Or.inr rfl⟩
  · have hjk : j < k.1 := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm k.2)
    exact ⟨⟨(j, k.1), hjk⟩, Or.inl rfl⟩

@[simp] theorem incidentPair_fst_snd {n : ℕ} (j : Fin n)
    (k : {k : Fin n // k ≠ j}) :
    ((incidentPair j k).1.1.1 = k.1 ∧ (incidentPair j k).1.1.2 = j) ∨
      ((incidentPair j k).1.1.1 = j ∧ (incidentPair j k).1.1.2 = k.1) := by
  classical
  unfold incidentPair
  split_ifs <;> simp

/-- Distinct particles give distinct incident ordered pairs. -/
theorem incidentPair_injective {n : ℕ} (j : Fin n) :
    Function.Injective (incidentPair j) := by
  intro a b hab
  unfold incidentPair at hab
  split at hab <;> split at hab <;> apply Subtype.ext <;> simp_all

/-- Every ordered pair incident to `j` arises from its other endpoint. -/
theorem incidentPair_surjective {n : ℕ} (j : Fin n) :
    Function.Surjective (incidentPair j) := by
  intro ik
  rcases ik.2 with hjfst | hjsnd
  · let k : {k : Fin n // k ≠ j} :=
      ⟨ik.1.1.2, by
        intro h
        exact (ne_of_gt ik.1.2) (h.trans hjfst)⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    unfold incidentPair
    dsimp only [k]
    rw [dite_eq_right (by
      intro h
      exact (not_lt_of_ge (le_of_lt ik.1.2)) (lt_of_lt_of_eq h hjfst))]
    simp [hjfst]
  · let k : {k : Fin n // k ≠ j} :=
      ⟨ik.1.1.1, by
        intro h
        exact (ne_of_gt ik.1.2) (h.trans hjsnd).symm⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    unfold incidentPair
    dsimp only [k]
    rw [dite_eq_left (by simpa [hjsnd] using ik.1.2)]
    simp [hjsnd]

/-- The explicit incident-pair parametrization is an equivalence. -/
def incidentPairEquiv {n : ℕ} (j : Fin n) :
    {k : Fin n // k ≠ j} ≃ IncidentVandermondePair j :=
  Equiv.ofBijective (incidentPair j)
    ⟨incidentPair_injective j, incidentPair_surjective j⟩

/-- The logarithmic-derivative summand attached to an incident ordered pair
has a uniform expression independent of which endpoint is smaller. -/
theorem incidentPair_logDerivative_summand {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n)
    (k : {k : Fin n // k ≠ j}) (w : ℂ) :
    (if j = (incidentPair j k).1.1.2 then w
      else if j = (incidentPair j k).1.1.1 then -w else 0) /
        (z (incidentPair j k).1.1.2 - z (incidentPair j k).1.1.1) =
      w / (z j - z k.1) := by
  classical
  unfold incidentPair
  by_cases h : k.1 < j
  · rw [dite_eq_left h]
    simp
  · rw [dite_eq_right h]
    dsimp only
    have hjk : j < k.1 := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm k.2)
    have hne : z j - z k.1 ≠ 0 :=
      sub_ne_zero.mpr (fun heq => k.2 (hz heq).symm)
    have hjkne : j ≠ k.1 := ne_of_lt hjk
    rw [ite_eq_right hjkne, ite_eq_left rfl]
    rw [show z k.1 - z j = -(z j - z k.1) by ring]
    field_simp

/-- Reindexing the logarithmic-derivative sum over incident pairs by their
other endpoint. -/
theorem sum_incidentPair_logDerivative {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) (w : ℂ) :
    (∑ ik : IncidentVandermondePair j,
      (if j = ik.1.1.2 then w else if j = ik.1.1.1 then -w else 0) /
        (z ik.1.1.2 - z ik.1.1.1)) =
      ∑ k : {k : Fin n // k ≠ j}, w / (z j - z k.1) := by
  rw [← (incidentPairEquiv j).sum_comp]
  apply Finset.sum_congr rfl
  intro k hk
  exact incidentPair_logDerivative_summand z hz j k w

/-- Nonincident ordered pairs contribute zero, so the full ordered-pair sum
is the sum over particles distinct from `j`. -/
theorem sum_vandermondePair_logDerivative {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) (w : ℂ) :
    (∑ ik : VandermondePair n,
      (if j = ik.1.2 then w else if j = ik.1.1 then -w else 0) /
        (z ik.1.2 - z ik.1.1)) =
      ∑ k : {k : Fin n // k ≠ j}, w / (z j - z k.1) := by
  calc
    _ = ∑ ik : IncidentVandermondePair j,
        (if j = ik.1.1.2 then w else if j = ik.1.1.1 then -w else 0) /
          (z ik.1.1.2 - z ik.1.1.1) := by
      have hsub :
          (∑ ik ∈ Finset.univ.filter (fun ik : VandermondePair n =>
              j = ik.1.1 ∨ j = ik.1.2),
            (if j = ik.1.2 then w else if j = ik.1.1 then -w else 0) /
              (z ik.1.2 - z ik.1.1)) =
          ∑ ik : IncidentVandermondePair j,
            (if j = ik.1.1.2 then w else if j = ik.1.1.1 then -w else 0) /
              (z ik.1.1.2 - z ik.1.1.1) :=
        Finset.sum_subtype _ (by simp) _
      rw [← hsub]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ik hik
      split_ifs <;> simp_all
    _ = _ := sum_incidentPair_logDerivative z hz j w

/-- Collision-free logarithmic derivative of the Vandermonde, indexed by
all particles other than the differentiated coordinate. -/
theorem fderiv_vandermonde_apply_coordinateDirection {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) (w : ℂ) :
    fderiv ℝ vandermonde z (coordinateDirection j w) =
      vandermonde z * ∑ k ∈ Finset.univ.erase j, w / (z j - z k) := by
  rw [fderiv_vandermonde_apply_coordinateDirection_eq_pairSum z hz j w,
    sum_vandermondePair_logDerivative z hz j w]
  congr 1
  symm
  exact Finset.sum_subtype (Finset.univ.erase j)
    (fun k => by simp [ne_comm]) (fun k => w / (z j - z k))

/-- Directional derivative of the squared modulus of the Vandermonde. -/
theorem fderiv_vandermondeWeight_apply {n : ℕ}
    (z v : Configuration n) :
    fderiv ℝ vandermondeWeight z v =
      2 * (conj (vandermonde z) * (fderiv ℝ vandermonde z v)).re := by
  have hV : DifferentiableAt ℝ vandermonde z :=
    (contDiff_vandermonde n).differentiable (by simp) |>.differentiableAt
  have hre := Complex.reCLM.hasFDerivAt.comp z hV.hasFDerivAt
  have him := Complex.imCLM.hasFDerivAt.comp z hV.hasFDerivAt
  have hsq := (hre.mul hre).add (him.mul him)
  rw [show vandermondeWeight = fun y : Configuration n =>
      (vandermonde y).re * (vandermonde y).re +
        (vandermonde y).im * (vandermonde y).im by
    funext y
    rw [vandermondeWeight, Complex.normSq_apply]]
  change fderiv ℝ
      (Complex.reCLM ∘ vandermonde * Complex.reCLM ∘ vandermonde +
        Complex.imCLM ∘ vandermonde * Complex.imCLM ∘ vandermonde) z v = _
  rw [hsq.fderiv]
  simp only [add_apply, smul_apply]
  simp [Complex.mul_re]
  ring

/-- Directional derivative of the configuration squared norm. -/
theorem contDiff_configurationNormSq {n : ℕ} :
    ContDiff ℝ ∞ (configurationNormSq : Configuration n → ℝ) := by
  unfold configurationNormSq
  simp_rw [Complex.normSq_apply]
  apply ContDiff.sum
  intro i hi
  have hp : ContDiff ℝ ∞ (fun z : Configuration n => z i) :=
    (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).contDiff
  exact ((Complex.reCLM.contDiff.comp hp).mul (Complex.reCLM.contDiff.comp hp)).add
    ((Complex.imCLM.contDiff.comp hp).mul (Complex.imCLM.contDiff.comp hp))

theorem fderiv_configurationNormSq_apply {n : ℕ}
    (z v : Configuration n) :
    fderiv ℝ configurationNormSq z v =
      2 * ∑ i : Fin n, (conj (z i) * v i).re := by
  unfold configurationNormSq
  rw [fderiv_fun_sum]
  · simp only [sum_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    let P : Configuration n →L[ℝ] ℂ :=
      ContinuousLinearMap.proj i
    have hre := Complex.reCLM.hasFDerivAt.comp z P.hasFDerivAt
    have him := Complex.imCLM.hasFDerivAt.comp z P.hasFDerivAt
    have hsq := (hre.mul hre).add (him.mul him)
    rw [show (fun y : Configuration n => Complex.normSq (y i)) =
        fun y => (y i).re * (y i).re + (y i).im * (y i).im by
      funext y
      rw [Complex.normSq_apply]]
    change fderiv ℝ
      (Complex.reCLM ∘ P * Complex.reCLM ∘ P +
        Complex.imCLM ∘ P * Complex.imCLM ∘ P) z v = _
    rw [hsq.fderiv]
    simp [P, Complex.mul_re]
    ring
  · intro i hi
    have hp : Differentiable ℝ (fun y : Configuration n => y i) :=
      (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).differentiable
    have hre := Complex.reCLM.differentiable.comp hp
    have him := Complex.imCLM.differentiable.comp hp
    rw [show (fun y : Configuration n => Complex.normSq (y i)) =
        fun y => (y i).re * (y i).re + (y i).im * (y i).im by
      funext y
      rw [Complex.normSq_apply]]
    change DifferentiableAt ℝ
      (Complex.reCLM ∘ (fun y : Configuration n => y i) *
        Complex.reCLM ∘ (fun y : Configuration n => y i) +
        Complex.imCLM ∘ (fun y : Configuration n => y i) *
        Complex.imCLM ∘ (fun y : Configuration n => y i)) z
    exact ((hre.mul hre).add (him.mul him)).differentiableAt

/-- Directional derivative of the Gaussian factor. -/
theorem fderiv_gaussianWeight_apply {n : ℕ} (z v : Configuration n) :
    fderiv ℝ (gaussianWeight n) z v =
      gaussianWeight n z * (-(n : ℝ) * fderiv ℝ configurationNormSq z v) := by
  have hnorm : DifferentiableAt ℝ configurationNormSq z :=
    (contDiff_configurationNormSq.differentiable (by simp)).differentiableAt
  have hin := hnorm.hasFDerivAt.const_mul (-(n : ℝ))
  have hexp := (Real.hasDerivAt_exp (-(n : ℝ) * configurationNormSq z)).comp_hasFDerivAt
    z hin
  unfold gaussianWeight
  change fderiv ℝ (Real.exp ∘ fun y => -(n : ℝ) * configurationNormSq y) z v = _
  rw [hexp.fderiv]
  simp only [smul_apply, smul_eq_mul]

/-- Real-coordinate derivative of the Gaussian factor. -/
theorem fderiv_gaussianWeight_realCoordinate {n : ℕ}
    (z : Configuration n) (j : Fin n) :
    fderiv ℝ (gaussianWeight n) z (realCoordinateDirection j) =
      -2 * n * (z j).re * gaussianWeight n z := by
  rw [fderiv_gaussianWeight_apply, fderiv_configurationNormSq_apply]
  simp only [realCoordinateDirection, coordinateDirection]
  rw [show (∑ x : Fin n, (conj (z x) * if x = j then 1 else 0).re) =
      (z j).re by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [hbj]
    · simp]
  ring

/-- Imaginary-coordinate derivative of the Gaussian factor. -/
theorem fderiv_gaussianWeight_imaginaryCoordinate {n : ℕ}
    (z : Configuration n) (j : Fin n) :
    fderiv ℝ (gaussianWeight n) z (imaginaryCoordinateDirection j) =
      -2 * n * (z j).im * gaussianWeight n z := by
  rw [fderiv_gaussianWeight_apply, fderiv_configurationNormSq_apply]
  simp only [imaginaryCoordinateDirection, coordinateDirection]
  rw [show (∑ x : Fin n, (conj (z x) * if x = j then Complex.I else 0).re) =
      (z j).im by
    rw [Finset.sum_eq_single j]
    · simp [Complex.mul_re]
    · intro b hb hbj
      simp [hbj]
    · simp]
  ring

/-- Collision-free logarithmic derivative of the Vandermonde weight. -/
theorem fderiv_vandermondeWeight_apply_coordinateDirection {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) (w : ℂ) :
    fderiv ℝ vandermondeWeight z (coordinateDirection j w) =
      2 * vandermondeWeight z *
        (∑ k ∈ Finset.univ.erase j, w / (z j - z k)).re := by
  rw [fderiv_vandermondeWeight_apply,
    fderiv_vandermonde_apply_coordinateDirection z hz]
  unfold vandermondeWeight
  rw [← mul_assoc, ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  ring

/-- Potential-gradient drift in a real coordinate.  The pregenerator uses
the negative of this coefficient. -/
def ginibreRealDriftCoordinate (n : ℕ) (j : Fin n)
    (z : Configuration n) : ℝ :=
  2 * (z j).re - (2 / (n : ℝ)) *
    ∑ k ∈ Finset.univ.erase j, ((z j - z k)⁻¹).re

/-- Potential-gradient drift in an imaginary coordinate. -/
def ginibreImagDriftCoordinate (n : ℕ) (j : Fin n)
    (z : Configuration n) : ℝ :=
  2 * (z j).im + (2 / (n : ℝ)) *
    ∑ k ∈ Finset.univ.erase j, ((z j - z k)⁻¹).im

/-- A complex coordinate direction, viewed over `ℝ`, splits into its real
and imaginary coordinate directions. -/
theorem coordinateDirection_eq_re_smul_real_add_im_smul_imaginary {n : ℕ}
    (j : Fin n) (w : ℂ) :
    coordinateDirection j w =
      w.re • realCoordinateDirection j +
        w.im • imaginaryCoordinateDirection j := by
  ext k
  by_cases h : k = j
  · subst k
    simp [coordinateDirection, realCoordinateDirection,
      imaginaryCoordinateDirection]
  · simp [coordinateDirection, realCoordinateDirection,
      imaginaryCoordinateDirection, h]

/-- The confinement directional derivative is the dot product with the
real and imaginary particle coordinates. -/
theorem fderiv_coordinateDirection_self {n : ℕ}
    (f : Configuration n → ℝ) (z : Configuration n) (j : Fin n) :
    fderiv ℝ f z (coordinateDirection j (z j)) =
      (z j).re * fderiv ℝ f z (realCoordinateDirection j) +
        (z j).im * fderiv ℝ f z (imaginaryCoordinateDirection j) := by
  rw [coordinateDirection_eq_re_smul_real_add_im_smul_imaginary]
  simp

/-- One unordered Coulomb-pair direction is exactly the difference of its
two endpoint real/imaginary inverse-distance drifts. -/
theorem fderiv_coulombPairDirection_eq_inverse_components {n : ℕ}
    (f : Configuration n → ℝ) (z : Configuration n) (i k : Fin n) :
    fderiv ℝ f z (coulombPairDirection i k z) =
      ((z i - z k)⁻¹).re *
          (fderiv ℝ f z (realCoordinateDirection i) -
            fderiv ℝ f z (realCoordinateDirection k)) -
        ((z i - z k)⁻¹).im *
          (fderiv ℝ f z (imaginaryCoordinateDirection i) -
            fderiv ℝ f z (imaginaryCoordinateDirection k)) := by
  unfold coulombPairDirection
  rw [map_sub]
  rw [coordinateDirection_eq_re_smul_real_add_im_smul_imaginary,
    coordinateDirection_eq_re_smul_real_add_im_smul_imaginary]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [Complex.inv_re, Complex.inv_im]
  simp only [Complex.div_ofReal_re, Complex.div_ofReal_im]
  ring

/-- Reindex an ordered off-diagonal sum as the two orientations of every
strictly ordered pair. -/
theorem sum_erase_eq_sum_Ioi_add_swap {n : ℕ} (F : Fin n → Fin n → ℝ) :
    ∑ j : Fin n, ∑ k ∈ Finset.univ.erase j, F j k =
      ∑ j : Fin n, ∑ k ∈ Finset.Ioi j, (F j k + F k j) := by
  have herase (j : Fin n) : Finset.univ.erase j =
      Finset.Iio j ∪ Finset.Ioi j := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_univ,
      Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi]
    simp
  have hdis (j : Fin n) : Disjoint (Finset.Iio j) (Finset.Ioi j) := by
    rw [Finset.disjoint_left]
    intro k hkio hkoi
    rw [Finset.mem_Iio] at hkio
    rw [Finset.mem_Ioi] at hkoi
    exact asymm hkio hkoi
  simp_rw [herase, Finset.sum_union (hdis _)]
  rw [Finset.sum_add_distrib]
  have htranspose :
      (∑ j : Fin n, ∑ k ∈ Finset.Iio j, F j k) =
        ∑ j : Fin n, ∑ k ∈ Finset.Ioi j, F k j := by
    calc
      _ = ∑ j : Fin n, ∑ k : Fin n, if k < j then F j k else 0 := by
        congr 1
        funext j
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext k
          simp
        · intro k hk
          rfl
      _ = ∑ k : Fin n, ∑ j : Fin n, if k < j then F j k else 0 :=
        Finset.sum_comm
      _ = _ := by
        congr 1
        funext k
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext j
          simp
        · intro j hj
          rfl
  rw [htranspose]
  simp_rw [Finset.sum_add_distrib]
  ring

/-- The coordinate drift dot gradient is the confinement contribution minus
the unordered-pair Coulomb contribution. -/
theorem sum_ginibreDrift_mul_fderiv {n : ℕ} (f : Configuration n → ℝ)
    (z : Configuration n) :
    ∑ j : Fin n,
        (ginibreRealDriftCoordinate n j z *
            fderiv ℝ f z (realCoordinateDirection j) +
          ginibreImagDriftCoordinate n j z *
            fderiv ℝ f z (imaginaryCoordinateDirection j)) =
      2 * ∑ j : Fin n, fderiv ℝ f z (coordinateDirection j (z j)) -
        (2 / (n : ℝ)) * ∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
          fderiv ℝ f z (coulombPairDirection j k z) := by
  let F : Fin n → Fin n → ℝ := fun j k =>
    ((z j - z k)⁻¹).re * fderiv ℝ f z (realCoordinateDirection j) -
      ((z j - z k)⁻¹).im * fderiv ℝ f z (imaginaryCoordinateDirection j)
  have hp (j k : Fin n) : F j k + F k j =
      fderiv ℝ f z (coulombPairDirection j k z) := by
    rw [fderiv_coulombPairDirection_eq_inverse_components]
    unfold F
    rw [show z k - z j = -(z j - z k) by abel, inv_neg]
    simp only [Complex.neg_re, Complex.neg_im]
    ring
  unfold ginibreRealDriftCoordinate ginibreImagDriftCoordinate
  simp_rw [fderiv_coordinateDirection_self]
  simp_rw [← hp]
  rw [← sum_erase_eq_sum_Ioi_add_swap F]
  have hF (j : Fin n) : (∑ k ∈ Finset.univ.erase j, F j k) =
      (∑ k ∈ Finset.univ.erase j, ((z j - z k)⁻¹).re) *
          fderiv ℝ f z (realCoordinateDirection j) -
        (∑ k ∈ Finset.univ.erase j, ((z j - z k)⁻¹).im) *
          fderiv ℝ f z (imaginaryCoordinateDirection j) := by
    unfold F
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  simp_rw [hF]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact drift-coordinate form of the Ginibre pregenerator. -/
theorem ginibrePregenerator_eq_laplacian_sub_drift {n : ℕ}
    (f : Configuration n → ℝ) (z : Configuration n) :
    ginibrePregenerator n f z =
      (1 / (n : ℝ)) * configurationLaplacian f z -
        ∑ j : Fin n,
          (ginibreRealDriftCoordinate n j z *
              fderiv ℝ f z (realCoordinateDirection j) +
            ginibreImagDriftCoordinate n j z *
              fderiv ℝ f z (imaginaryCoordinateDirection j)) := by
  rw [sum_ginibreDrift_mul_fderiv]
  unfold ginibrePregenerator
  ring

private theorem differentiableAt_vandermondeWeight {n : ℕ}
    (z : Configuration n) : DifferentiableAt ℝ vandermondeWeight z := by
  rw [show vandermondeWeight = fun y : Configuration n =>
      (vandermonde y).re * (vandermonde y).re +
        (vandermonde y).im * (vandermonde y).im by
    funext y
    rw [vandermondeWeight, Complex.normSq_apply]]
  have hV := (contDiff_vandermonde n).differentiable (by simp)
  fun_prop

private theorem differentiableAt_gaussianWeight (n : ℕ)
    (z : Configuration n) : DifferentiableAt ℝ (gaussianWeight n) z := by
  unfold gaussianWeight
  have h : ContDiff ℝ ∞ (fun y : Configuration n =>
      Real.exp (-(n : ℝ) * configurationNormSq y)) := by
    simpa only [neg_mul] using
      (((contDiff_const : ContDiff ℝ ∞
        (fun _ : Configuration n => (n : ℝ))).mul
          contDiff_configurationNormSq).neg.exp)
  exact (h.differentiable (by simp)).differentiableAt

/-- Real-coordinate logarithmic derivative of the full Ginibre Lebesgue
density. -/
theorem fderiv_ginibreLebesgueDensityReal_realCoordinate {n : ℕ}
    (hn : 0 < n) (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    fderiv ℝ (ginibreLebesgueDensityReal n) z (realCoordinateDirection j) =
      -(n : ℝ) * ginibreLebesgueDensityReal n z *
        ginibreRealDriftCoordinate n j z := by
  unfold ginibreLebesgueDensityReal
  rw [show (fun y : Configuration n =>
      (n / Real.pi) ^ n * vandermondeWeight y * gaussianWeight n y) =
      fun y => (n / Real.pi) ^ n *
        (vandermondeWeight y * gaussianWeight n y) by funext y; ring]
  change fderiv ℝ (fun y : Configuration n =>
    (n / Real.pi) ^ n *
      ((vandermondeWeight : Configuration n → ℝ) * gaussianWeight n) y) z _ = _
  rw [fderiv_const_mul
    ((differentiableAt_vandermondeWeight z).mul
      (differentiableAt_gaussianWeight n z))]
  rw [fderiv_mul (differentiableAt_vandermondeWeight z)
    (differentiableAt_gaussianWeight n z)]
  simp only [smul_apply, add_apply, smul_eq_mul]
  change _ * (_ * fderiv ℝ (gaussianWeight n) z (realCoordinateDirection j) +
    _ * fderiv ℝ vandermondeWeight z (coordinateDirection j 1)) = _
  rw [fderiv_vandermondeWeight_apply_coordinateDirection z hz j 1,
    fderiv_gaussianWeight_realCoordinate]
  simp_rw [one_div]
  unfold ginibreRealDriftCoordinate
  have hs : (∑ k ∈ Finset.univ.erase j, (z j - z k)⁻¹).re =
      ∑ k ∈ Finset.univ.erase j, ((z j - z k)⁻¹).re := by
    change Complex.reCLM (∑ k ∈ Finset.univ.erase j, (z j - z k)⁻¹) = _
    exact map_sum Complex.reCLM _ _
  rw [hs]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']
  ring

/-- Imaginary-coordinate logarithmic derivative of the full Ginibre
Lebesgue density. -/
theorem fderiv_ginibreLebesgueDensityReal_imaginaryCoordinate {n : ℕ}
    (hn : 0 < n) (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    fderiv ℝ (ginibreLebesgueDensityReal n) z (imaginaryCoordinateDirection j) =
      -(n : ℝ) * ginibreLebesgueDensityReal n z *
        ginibreImagDriftCoordinate n j z := by
  unfold ginibreLebesgueDensityReal
  rw [show (fun y : Configuration n =>
      (n / Real.pi) ^ n * vandermondeWeight y * gaussianWeight n y) =
      fun y => (n / Real.pi) ^ n *
        (vandermondeWeight y * gaussianWeight n y) by funext y; ring]
  change fderiv ℝ (fun y : Configuration n =>
    (n / Real.pi) ^ n *
      ((vandermondeWeight : Configuration n → ℝ) * gaussianWeight n) y) z _ = _
  rw [fderiv_const_mul
    ((differentiableAt_vandermondeWeight z).mul
      (differentiableAt_gaussianWeight n z))]
  rw [fderiv_mul (differentiableAt_vandermondeWeight z)
    (differentiableAt_gaussianWeight n z)]
  simp only [smul_apply, add_apply, smul_eq_mul]
  change _ * (_ * fderiv ℝ (gaussianWeight n) z (imaginaryCoordinateDirection j) +
    _ * fderiv ℝ vandermondeWeight z (coordinateDirection j Complex.I)) = _
  rw [fderiv_vandermondeWeight_apply_coordinateDirection z hz j Complex.I,
    fderiv_gaussianWeight_imaginaryCoordinate]
  simp_rw [div_eq_mul_inv]
  unfold ginibreImagDriftCoordinate
  have hs : (∑ k ∈ Finset.univ.erase j,
      Complex.I * (z j - z k)⁻¹).re =
      -(∑ k ∈ Finset.univ.erase j, ((z j - z k)⁻¹).im) := by
    change Complex.reCLM (∑ k ∈ Finset.univ.erase j,
      Complex.I * (z j - z k)⁻¹) = _
    rw [map_sum]
    simp [Complex.mul_re]
  rw [hs]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']
  ring

/-- Pointwise divergence form of the Ginibre pregenerator away from particle
collisions. -/
theorem ginibreLebesgueDensityReal_mul_pregenerator_eq_divergence {n : ℕ}
    (hn : 0 < n) (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f)
    (z : Configuration n) (hz : CollisionFree z) :
    ginibreLebesgueDensityReal n z * ginibrePregenerator n f z =
      (1 / (n : ℝ)) * ∑ j : Fin n,
        (fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (realCoordinateDirection j)) z
              (realCoordinateDirection j) +
          fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (imaginaryCoordinateDirection j)) z
              (imaginaryCoordinateDirection j)) := by
  have hdir (v : Configuration n) :
      DifferentiableAt ℝ (fun y => fderiv ℝ f y v) z := by
    have hp : ContDiff ℝ ∞ (fun y : Configuration n => (y, v)) :=
      contDiff_id.prodMk contDiff_const
    exact ((hf.contDiff_fderiv_apply (m := ∞) (by simp)).comp hp).differentiable
      (by simp) z
  have hprod (v : Configuration n) :
      fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
          fderiv ℝ f y v) z v =
        ginibreLebesgueDensityReal n z * secondDirectionalDerivative f v z +
          fderiv ℝ (ginibreLebesgueDensityReal n) z v * fderiv ℝ f z v := by
    change fderiv ℝ
      ((ginibreLebesgueDensityReal n) * fun y => fderiv ℝ f y v) z v = _
    rw [fderiv_mul ((contDiff_ginibreLebesgueDensityReal n).differentiable
      (by simp) z)
      (hdir v)]
    simp only [smul_apply, add_apply, smul_eq_mul]
    unfold secondDirectionalDerivative
    ring
  simp_rw [hprod]
  simp_rw [fderiv_ginibreLebesgueDensityReal_realCoordinate hn z hz,
    fderiv_ginibreLebesgueDensityReal_imaginaryCoordinate hn z hz]
  rw [ginibrePregenerator_eq_laplacian_sub_drift]
  unfold configurationLaplacian
  field_simp [Nat.cast_ne_zero.mpr hn.ne']
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Each density-weighted directional flux of a core observable is smooth. -/
theorem contDiff_ginibreDirectionalFlux_core {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f)
    (v : Configuration n) :
    ContDiff ℝ ∞ (fun z => ginibreLebesgueDensityReal n z *
      fderiv ℝ f z v) := by
  apply (contDiff_ginibreLebesgueDensityReal n).mul
  have hp : ContDiff ℝ ∞ (fun z : Configuration n => (z, v)) :=
    contDiff_id.prodMk contDiff_const
  exact (hf.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp hp

/-- Each density-weighted directional flux of a core observable has compact
support (contained in the support of the derivative of the observable). -/
theorem hasCompactSupport_ginibreDirectionalFlux_core {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f)
    (v : Configuration n) :
    HasCompactSupport (fun z => ginibreLebesgueDensityReal n z *
      fderiv ℝ f z v) := by
  exact (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hf.2.1 v).mul_left

/-- The directional derivative of every density-weighted core flux is
Lebesgue integrable. -/
theorem integrable_fderiv_ginibreDirectionalFlux_core {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f)
    (v : Configuration n) :
    Integrable (fun z => fderiv ℝ
      (fun y => ginibreLebesgueDensityReal n y * fderiv ℝ f y v) z v)
      volume := by
  have hs := hasCompactSupport_ginibreDirectionalFlux_core hf v
  have hds : HasCompactSupport (fun z => fderiv ℝ
      (fun y => ginibreLebesgueDensityReal n y * fderiv ℝ f y v) z v) :=
    HasCompactSupport.fderiv_apply (𝕜 := ℝ) hs v
  have hc : Continuous (fun z => fderiv ℝ
      (fun y => ginibreLebesgueDensityReal n y * fderiv ℝ f y v) z v) :=
    ((contDiff_ginibreDirectionalFlux_core hf v).continuous_fderiv (by simp)).clm_apply
      continuous_const
  exact hc.integrable_of_hasCompactSupport hds

/-- Product-rule identity for the density-weighted directional flux times
the observable. -/
theorem fderiv_core_mul_ginibreDirectionalFlux {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f)
    (v : Configuration n) (z : Configuration n) :
    fderiv ℝ (fun y => f y *
      (ginibreLebesgueDensityReal n y * fderiv ℝ f y v)) z v =
      ginibreLebesgueDensityReal n z * (fderiv ℝ f z v) ^ 2 +
        f z * fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
          fderiv ℝ f y v) z v := by
  have hflux : DifferentiableAt ℝ (fun y => ginibreLebesgueDensityReal n y *
      fderiv ℝ f y v) z :=
    ((contDiff_ginibreDirectionalFlux_core hf v).differentiable (by simp) z)
  change fderiv ℝ (f * fun y => ginibreLebesgueDensityReal n y *
    fderiv ℝ f y v) z v = _
  rw [fderiv_mul (hf.1.differentiable (by simp) z) hflux]
  simp only [smul_apply, add_apply, smul_eq_mul]
  ring

/-- The density-weighted flux times a core observable remains smooth and
compactly supported. -/
theorem contDiff_hasCompactSupport_core_mul_ginibreDirectionalFlux {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f)
    (v : Configuration n) :
    ContDiff ℝ ∞ (fun z => f z *
        (ginibreLebesgueDensityReal n z * fderiv ℝ f z v)) ∧
      HasCompactSupport (fun z => f z *
        (ginibreLebesgueDensityReal n z * fderiv ℝ f z v)) := by
  exact ⟨hf.1.mul (contDiff_ginibreDirectionalFlux_core hf v),
    hf.2.1.mul_right⟩

private theorem integral_density_directional_sq_eq_neg_flux
    {n : ℕ} {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f)
    (v : Configuration n)
    (hzero : ∫ z, fderiv ℝ (fun y => f y *
      (ginibreLebesgueDensityReal n y * fderiv ℝ f y v)) z v = 0) :
    ∫ z, ginibreLebesgueDensityReal n z * (fderiv ℝ f z v) ^ 2 =
      - ∫ z, f z * fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
        fderiv ℝ f y v) z v := by
  have hA : Integrable (fun z => ginibreLebesgueDensityReal n z *
      (fderiv ℝ f z v) ^ 2) := by
    apply ((contDiff_ginibreLebesgueDensityReal n).continuous.mul
      (((hf.1.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2))
      |>.integrable_of_hasCompactSupport
    have hs := HasCompactSupport.fderiv_apply (𝕜 := ℝ) hf.2.1 v
    simpa only [pow_two] using hs.mul_right.mul_left
  have hB : Integrable (fun z => f z * fderiv ℝ
      (fun y => ginibreLebesgueDensityReal n y * fderiv ℝ f y v) z v) := by
    have hc : Continuous (fun z => fderiv ℝ
        (fun y => ginibreLebesgueDensityReal n y * fderiv ℝ f y v) z v) :=
      ((contDiff_ginibreDirectionalFlux_core hf v).continuous_fderiv (by simp)).clm_apply
        continuous_const
    exact (hf.1.continuous.mul hc).integrable_of_hasCompactSupport hf.2.1.mul_right
  have hs : (∫ z, ginibreLebesgueDensityReal n z * (fderiv ℝ f z v) ^ 2) +
      ∫ z, f z * fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
        fderiv ℝ f y v) z v = 0 := by
    rw [← integral_add hA hB]
    rw [← hzero]
    apply integral_congr_ae
    filter_upwards with z
    exact (fderiv_core_mul_ginibreDirectionalFlux hf v z).symm
  linarith

theorem integral_density_realDirectional_sq_eq_neg_flux {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) (j : Fin n) :
    ∫ z, ginibreLebesgueDensityReal n z *
        (fderiv ℝ f z (realCoordinateDirection j)) ^ 2 =
      - ∫ z, f z * fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
        fderiv ℝ f y (realCoordinateDirection j)) z
          (realCoordinateDirection j) := by
  apply integral_density_directional_sq_eq_neg_flux hf
  let hc := contDiff_hasCompactSupport_core_mul_ginibreDirectionalFlux hf
    (realCoordinateDirection j)
  exact integral_fderiv_configuration_real_eq_zero _ (hc.1.of_le (by simp)) hc.2 j

theorem integral_density_imagDirectional_sq_eq_neg_flux {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) (j : Fin n) :
    ∫ z, ginibreLebesgueDensityReal n z *
        (fderiv ℝ f z (imaginaryCoordinateDirection j)) ^ 2 =
      - ∫ z, f z * fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
        fderiv ℝ f y (imaginaryCoordinateDirection j)) z
          (imaginaryCoordinateDirection j) := by
  apply integral_density_directional_sq_eq_neg_flux hf
  let hc := contDiff_hasCompactSupport_core_mul_ginibreDirectionalFlux hf
    (imaginaryCoordinateDirection j)
  exact integral_fderiv_configuration_imag_eq_zero _ (hc.1.of_le (by simp)) hc.2 j

/-- Summed coordinate form of the density-weighted integration-by-parts
identity. -/
theorem sum_integral_density_gradient_sq_eq_neg_flux {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) :
    ∑ j : Fin n,
        ((∫ z, ginibreLebesgueDensityReal n z *
            (fderiv ℝ f z (realCoordinateDirection j)) ^ 2) +
          ∫ z, ginibreLebesgueDensityReal n z *
            (fderiv ℝ f z (imaginaryCoordinateDirection j)) ^ 2) =
      - ∑ j : Fin n,
        ((∫ z, f z * fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (realCoordinateDirection j)) z
              (realCoordinateDirection j)) +
          ∫ z, f z * fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (imaginaryCoordinateDirection j)) z
              (imaginaryCoordinateDirection j)) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_density_realDirectional_sq_eq_neg_flux hf j,
    integral_density_imagDirectional_sq_eq_neg_flux hf j]
  ring

theorem sum_density_directional_sq_eq_realGradientNormSq {n : ℕ}
    (f : Configuration n → ℝ) (z : Configuration n) :
    ∑ j : Fin n, ginibreLebesgueDensityReal n z *
        ((fderiv ℝ f z (realCoordinateDirection j)) ^ 2 +
          (fderiv ℝ f z (imaginaryCoordinateDirection j)) ^ 2) =
      ginibreLebesgueDensityReal n z * realGradientNormSq f z := by
  simp [realGradientNormSq, Finset.mul_sum]

theorem sum_core_flux_divergence_eq_density_mul_pregenerator {n : ℕ}
    (hn : 0 < n) {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f)
    (z : Configuration n) (hz : CollisionFree z) :
    ∑ j : Fin n, f z *
        (fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (realCoordinateDirection j)) z
              (realCoordinateDirection j) +
          fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (imaginaryCoordinateDirection j)) z
              (imaginaryCoordinateDirection j)) =
      (n : ℝ) * ginibreLebesgueDensityReal n z *
        f z * ginibrePregenerator n f z := by
  have hd := ginibreLebesgueDensityReal_mul_pregenerator_eq_divergence
    hn f hf.1 z hz
  field_simp [Nat.cast_ne_zero.mpr hn.ne'] at hd
  calc
    _ = f z * ∑ j : Fin n,
        (fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (realCoordinateDirection j)) z
              (realCoordinateDirection j) +
          fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (imaginaryCoordinateDirection j)) z
              (imaginaryCoordinateDirection j)) := by rw [Finset.mul_sum]
    _ = f z * (ginibreLebesgueDensityReal n z *
        ginibrePregenerator n f z * (n : ℝ)) := by rw [hd]
    _ = _ := by ring

/-- Unnormalized density form of the Ginibre generator integration-by-parts
identity. -/
theorem integral_density_gradient_eq_generator {n : ℕ} (hn : 0 < n)
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) :
    (∫ z, ginibreLebesgueDensityReal n z * realGradientNormSq f z) =
      -(n : ℝ) * ∫ z, ginibreLebesgueDensityReal n z * f z *
        ginibrePregenerator n f z := by
  let R : Fin n → Configuration n → ℝ := fun j z =>
    ginibreLebesgueDensityReal n z *
      (fderiv ℝ f z (realCoordinateDirection j)) ^ 2
  let I : Fin n → Configuration n → ℝ := fun j z =>
    ginibreLebesgueDensityReal n z *
      (fderiv ℝ f z (imaginaryCoordinateDirection j)) ^ 2
  let FR : Fin n → Configuration n → ℝ := fun j z =>
    f z * fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
      fderiv ℝ f y (realCoordinateDirection j)) z (realCoordinateDirection j)
  let FI : Fin n → Configuration n → ℝ := fun j z =>
    f z * fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
      fderiv ℝ f y (imaginaryCoordinateDirection j)) z
        (imaginaryCoordinateDirection j)
  have hR (j : Fin n) : Integrable (R j) := by
    apply ((contDiff_ginibreLebesgueDensityReal n).continuous.mul
      (((hf.1.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2))
      |>.integrable_of_hasCompactSupport
    have hs := HasCompactSupport.fderiv_apply (𝕜 := ℝ) hf.2.1
      (realCoordinateDirection j)
    simpa only [pow_two] using hs.mul_right.mul_left
  have hI (j : Fin n) : Integrable (I j) := by
    apply ((contDiff_ginibreLebesgueDensityReal n).continuous.mul
      (((hf.1.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2))
      |>.integrable_of_hasCompactSupport
    have hs := HasCompactSupport.fderiv_apply (𝕜 := ℝ) hf.2.1
      (imaginaryCoordinateDirection j)
    simpa only [pow_two] using hs.mul_right.mul_left
  have hFR (j : Fin n) : Integrable (FR j) := by
    apply (hf.1.continuous.mul
      (((contDiff_ginibreDirectionalFlux_core hf (realCoordinateDirection j)).continuous_fderiv
        (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
    exact hf.2.1.mul_right
  have hFI (j : Fin n) : Integrable (FI j) := by
    apply (hf.1.continuous.mul
      (((contDiff_ginibreDirectionalFlux_core hf (imaginaryCoordinateDirection j)).continuous_fderiv
        (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
    exact hf.2.1.mul_right
  have hsum := sum_integral_density_gradient_sq_eq_neg_flux hf
  change (∑ j : Fin n, ((∫ z, R j z) + ∫ z, I j z)) =
    -∑ j : Fin n, ((∫ z, FR j z) + ∫ z, FI j z) at hsum
  have hleft : (∑ j : Fin n, ((∫ z, R j z) + ∫ z, I j z)) =
      ∫ z, ginibreLebesgueDensityReal n z * realGradientNormSq f z := by
    calc
      _ = ∑ j : Fin n, ∫ z, (R j z + I j z) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_add (hR j) (hI j)]
      _ = ∫ z, ∑ j : Fin n, (R j z + I j z) := by
        rw [integral_finsetSum]
        intro j hj
        exact (hR j).add (hI j)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with z
        rw [← sum_density_directional_sq_eq_realGradientNormSq f z]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [R, I]
        ring
  have hright : (∑ j : Fin n, ((∫ z, FR j z) + ∫ z, FI j z)) =
      ∫ z, (n : ℝ) * ginibreLebesgueDensityReal n z * f z *
        ginibrePregenerator n f z := by
    calc
      _ = ∑ j : Fin n, ∫ z, (FR j z + FI j z) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_add (hFR j) (hFI j)]
      _ = ∫ z, ∑ j : Fin n, (FR j z + FI j z) := by
        rw [integral_finsetSum]
        intro j hj
        exact (hFR j).add (hFI j)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : CollisionFree z
        · simpa [FR, FI, mul_add] using
            sum_core_flux_divergence_eq_density_mul_pregenerator hn hf z hz
        · have hfz : f z = 0 := by
            by_contra hfne
            exact hz (hf.support_collisionFree hfne)
          simp [FR, FI, hfz]
  rw [hleft, hright] at hsum
  calc
    _ = -∫ z, (n : ℝ) * ginibreLebesgueDensityReal n z * f z *
        ginibrePregenerator n f z := hsum
    _ = -(n : ℝ) * ∫ z, ginibreLebesgueDensityReal n z * f z *
        ginibrePregenerator n f z := by
      have hc : (∫ z, (n : ℝ) * ginibreLebesgueDensityReal n z * f z *
          ginibrePregenerator n f z) =
          (n : ℝ) * ∫ z, ginibreLebesgueDensityReal n z * f z *
            ginibrePregenerator n f z := by
        rw [← integral_const_mul]
        congr 1
        funext z
        ring
      rw [hc]
      ring

/-- Concrete normalized Ginibre integration by parts on the collision-free
smooth symmetric core. -/
theorem ginibrePregenerator_integrationByParts {n : ℕ} (hn : 0 < n)
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) :
    (∫ z, ginibrePregenerator n f z * f z ∂ginibreMeasure n) =
      -smoothGinibreEnergy n f := by
  rw [integral_ginibreMeasure_eq_density_volume hn]
  unfold smoothGinibreEnergy
  rw [integral_ginibreMeasure_eq_density_volume hn]
  have h := integral_density_gradient_eq_generator hn hf
  have hswap : (∫ z, ginibreLebesgueDensityReal n z *
      (ginibrePregenerator n f z * f z)) =
      ∫ z, ginibreLebesgueDensityReal n z * f z *
        ginibrePregenerator n f z := by
    apply integral_congr_ae
    filter_upwards with z
    ring
  rw [hswap]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  calc
    (ginibreNormalizingMass n).toReal⁻¹ *
        (∫ z, ginibreLebesgueDensityReal n z * f z *
          ginibrePregenerator n f z) =
      -(1 / (n : ℝ)) * ((ginibreNormalizingMass n).toReal⁻¹ *
        ∫ z, ginibreLebesgueDensityReal n z * realGradientNormSq f z) := by
          rw [h]
          field_simp
    _ = _ := by ring

/-- The collision locus is also null for configuration Lebesgue measure. -/
theorem configurationVolume_collisionSet {n : ℕ} (hn : 0 < n) :
    configurationVolume n (collisionSet n) = 0 := by
  have hac : configurationVolume n ≪
      (configurationVolume n).withDensity (complexGaussianDensity n) := by
    apply withDensity_absolutelyContinuous'
    · exact (measurable_complexGaussianDensity n).aemeasurable
    · filter_upwards with z
      unfold complexGaussianDensity gaussianWeight
      positivity
  apply hac
  rw [← show complexGaussianDensityMeasure n =
      (configurationVolume n).withDensity (complexGaussianDensity n) by rfl]
  rw [← complexGaussianDensityIdentification n hn]
  exact complexGaussianMeasure_collisionSet n

/-- The concrete Ginibre pregenerator has zero mean on its smooth core. -/
theorem integral_ginibrePregenerator_eq_zero {n : ℕ} (hn : 0 < n)
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) :
    ∫ z, ginibrePregenerator n f z ∂ginibreMeasure n = 0 := by
  rw [integral_ginibreMeasure_eq_density_volume hn]
  have hcf : ∀ᵐ z ∂(configurationVolume n), CollisionFree z := by
    rw [ae_iff]
    have heq : {z : Configuration n | ¬ CollisionFree z} = collisionSet n := by
      ext z
      rw [Set.mem_ofPred_eq, collisionFree_iff_not_mem_collisionSet]
      simp
    rw [heq]
    exact configurationVolume_collisionSet hn
  have hdiv : (∫ z, ginibreLebesgueDensityReal n z *
      ginibrePregenerator n f z) =
      ∫ z, (1 / (n : ℝ)) * ∑ j : Fin n,
        (fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (realCoordinateDirection j)) z
              (realCoordinateDirection j) +
          fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (imaginaryCoordinateDirection j)) z
              (imaginaryCoordinateDirection j)) := by
    apply integral_congr_ae
    filter_upwards [hcf] with z hz
    exact ginibreLebesgueDensityReal_mul_pregenerator_eq_divergence
      hn f hf.1 z hz
  rw [hdiv, integral_const_mul, integral_finsetSum]
  · simp_rw [integral_add
        (integrable_fderiv_ginibreDirectionalFlux_core hf _)
        (integrable_fderiv_ginibreDirectionalFlux_core hf _)]
    have hzR (j : Fin n) :
        (∫ z, fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
          fderiv ℝ f y (realCoordinateDirection j)) z
            (realCoordinateDirection j)) = 0 :=
      integral_fderiv_configuration_real_eq_zero _
        ((contDiff_ginibreDirectionalFlux_core hf _).of_le (by simp))
        (hasCompactSupport_ginibreDirectionalFlux_core hf _) j
    have hzI (j : Fin n) :
        (∫ z, fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
          fderiv ℝ f y (imaginaryCoordinateDirection j)) z
            (imaginaryCoordinateDirection j)) = 0 :=
      integral_fderiv_configuration_imag_eq_zero _
        ((contDiff_ginibreDirectionalFlux_core hf _).of_le (by simp))
        (hasCompactSupport_ginibreDirectionalFlux_core hf _) j
    simp [hzR, hzI]
  · intro j hj
    exact (integrable_fderiv_ginibreDirectionalFlux_core hf _).add
      (integrable_fderiv_ginibreDirectionalFlux_core hf _)

/-- A compactly supported core observable is Ginibre-integrable. -/
theorem integrable_core_ginibre {n : ℕ} (hn : 0 < n)
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) :
    Integrable f (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact hf.1.continuous.integrable_of_hasCompactSupport hf.2.1

/-- The Euclidean squared gradient of a core observable is continuous. -/
theorem continuous_realGradientNormSq_of_core {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) :
    Continuous (realGradientNormSq f) := by
  unfold realGradientNormSq
  apply continuous_finsetSum
  intro k hk
  have hdf : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by simp)
  have hre : Continuous (fun z : Configuration n =>
      fderiv ℝ f z (realCoordinateDirection k)) :=
    hdf.clm_apply continuous_const
  have him : Continuous (fun z : Configuration n =>
      fderiv ℝ f z (imaginaryCoordinateDirection k)) :=
    hdf.clm_apply continuous_const
  exact hre.pow 2 |>.add (him.pow 2)

/-- The squared gradient vanishes off the compact support of a core
observable, hence is itself compactly supported. -/
theorem hasCompactSupport_realGradientNormSq_of_core {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) :
    HasCompactSupport (realGradientNormSq f) := by
  apply hf.2.1.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal
  · intro z hz
    by_contra hzt
    apply hz
    have hzero : fderiv ℝ f z = 0 := fderiv_of_notMem_tsupport ℝ hzt
    simp [realGradientNormSq, hzero]
  · exact isClosed_tsupport _

/-- The Dirichlet density of a core observable is Ginibre-integrable. -/
theorem integrable_realGradientNormSq_core_ginibre {n : ℕ} (hn : 0 < n)
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) :
    Integrable (realGradientNormSq f) (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact (continuous_realGradientNormSq_of_core hf).integrable_of_hasCompactSupport
    (hasCompactSupport_realGradientNormSq_of_core hf)

/-- The square of a compactly supported core observable is
Ginibre-integrable. -/
theorem integrable_sq_core_ginibre {n : ℕ} (hn : 0 < n)
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) :
    Integrable (fun z => (f z) ^ 2) (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  apply (hf.1.continuous.pow 2).integrable_of_hasCompactSupport
  apply hf.2.1.mono
  intro z hz hzero
  exact hz (by simp [hzero])

end
end GinibrePoincare
