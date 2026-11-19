/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceMatrixWeakClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftLSITransport
public import LeanPool.GinibrePoincare.Analysis.AlternativeMatrixPoincare
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevDensity
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradient
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevLocalIntegrability

/-! # From matrix H¹ membership to the intrinsic overlap inequalities

The graph closure initially supplies an L² value and entry-gradient tuple, not
an identification of that tuple with the derivative of a spectral observable.
Divide each compact test by the strictly positive Gaussian density: the resulting
pairing is continuous in Gaussian L², so integration by parts passes from compact
C¹ pairs to their closure and becomes the ordinary volume weak identity.

On any open set where the represented value is C¹, uniqueness of distributions
identifies the gradient tuple with its classical derivative almost everywhere.
Local eigenvalue branches make the symmetric lift C¹ on the open simple-spectrum
locus, whose complement has Gaussian measure zero. This proves the derivative
bridge from H¹ membership itself. The overlap-energy identity then proves overlap
integrability and transports the Gaussian variance and entropy bounds. The final
endpoint requires only the value-domain predicate `MatrixGaussianH1Function`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace GinibrePoincare
noncomputable section

/-- Division by the strictly positive Gaussian density converts an ordinary
compact test into an L² test for the matrix Gaussian law. -/
theorem correspondenceMatrix_test_memLp {n : ℕ} (hn : 0 < n)
    (θ : MatrixRealSpace n → ℝ) (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    MemLp (fun A => θ A / matrixGaussianDensityReal n A) 2 (matrixGaussianMeasure n) := by
  have : @IsProbabilityMeasure (MatrixRealSpace n)
      (inferInstance : MeasurableSpace (MatrixRealSpace n)) (matrixGaussianMeasure n) :=
    matrixGaussianMeasure_isProbability n
  have : @IsFiniteMeasureOnCompacts (MatrixRealSpace n)
      (inferInstance : MeasurableSpace (MatrixRealSpace n)) _ (matrixGaussianMeasure n) :=
    ⟨fun _ _ => measure_lt_top _ _⟩
  have hw : Continuous (matrixGaussianDensityReal n) := by
    unfold matrixGaussianDensityReal
    simp only [matrixHSNormSq_eq_sum]
    fun_prop
  have hdiv : Continuous (fun A : MatrixRealSpace n => θ A / matrixGaussianDensityReal n A) :=
    hθ.div hw (fun A => (matrixGaussianDensityReal_pos n hn A).ne')
  apply hdiv.memLp_of_hasCompactSupport
  have H : HasCompactSupport
      (fun A : MatrixRealSpace n => θ A * (matrixGaussianDensityReal n A)⁻¹) := hc.mul_right
  simpa only [div_eq_mul_inv] using H

/-- Exact ordinary-volume pairing recovered from the positive Gaussian density. -/
theorem correspondenceMatrix_test_integral {n : ℕ} (hn : 0 < n)
    (f θ : MatrixRealSpace n → ℝ) :
    (∫ A, f A * (θ A / matrixGaussianDensityReal n A) ∂matrixGaussianMeasure n) =
      ∫ A, f A * θ A := by
  rw [matrixGaussianMeasure_eq_withDensity hn,
    integral_withDensity_eq_integral_toReal_smul (measurable_matrixGaussianDensity n)
      (ae_of_all _ fun A => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact ae_of_all _ fun A => by
    change (ENNReal.ofReal (matrixGaussianDensityReal n A)).toReal *
      (f A * (θ A / matrixGaussianDensityReal n A)) = f A * θ A
    rw [ENNReal.toReal_ofReal (matrixGaussianDensityReal_pos n hn A).le]
    field_simp [(matrixGaussianDensityReal_pos n hn A).ne']

/-- Membership in the actual closed Gaussian matrix gradient graph implies the
ordinary distributional derivative equations; no weak-derivative certificate is
assumed. -/
theorem correspondenceMatrix_H1_weak {n : ℕ} (hn : 0 < n)
    (p : MatrixGaussianSobolevPair n) (hp : p ∈ matrixGaussianH1Completion n)
    (i : MatrixRealIndex n) (θ : MatrixRealSpace n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    (∫ A : MatrixRealSpace n, p.2 i A * θ A) =
      -(∫ A : MatrixRealSpace n,
        p.1 A * fderiv ℝ θ A (matrixRealCoordinates n (Pi.single i 1))) := by
  let : (volume : Measure (Fin 2 → ℝ)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi _
  let : (volume : Measure ℂ).IsAddHaarMeasure := by
    have h := Complex.volume_preserving_equiv_pi.symm Complex.measurableEquivPi
    rw [← h.map_eq]
    exact Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm.isAddHaarMeasure_map _
  let : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : (volume : Measure (MatrixRealSpace n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let v := matrixRealCoordinates n (Pi.single i 1)
  let w := matrixGaussianDensityReal n
  have hD : Continuous (fun A => fderiv ℝ θ A v) :=
    (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDc : HasCompactSupport (fun A => fderiv ℝ θ A v) := hc.fderiv_apply (𝕜 := ℝ) v
  -- Weighted L² pairings make the ordinary derivative identity closed.
  have hm1 : MemLp (fun A : Matrix (Fin n) (Fin n) ℂ => θ A / w A) 2 (matrixGaussianMeasure n) :=
    correspondenceMatrix_test_memLp hn θ hθ.continuous hc
  have hm2 : MemLp (fun A : Matrix (Fin n) (Fin n) ℂ => fderiv ℝ θ A v / w A) 2
      (matrixGaussianMeasure n) := correspondenceMatrix_test_memLp hn _ hD hDc
  have hclosed : IsClosed {q : MatrixGaussianSobolevPair n |
      (∫ A, q.2 i A * (θ A / w A) ∂matrixGaussianMeasure n) =
      -(∫ A, q.1 A * (fderiv ℝ θ A v / w A) ∂matrixGaussianMeasure n)} :=
    isClosed_eq
      ((continuous_L2_integral_mul _ _ hm1).comp ((continuous_apply i).comp continuous_snd))
      (((continuous_L2_integral_mul _ _ hm2).comp continuous_fst).neg)
  have hsub : matrixGaussianCompactC1Pairs n ⊆ {q : MatrixGaussianSobolevPair n |
      (∫ A, q.2 i A * (θ A / w A) ∂matrixGaussianMeasure n) =
      -(∫ A, q.1 A * (fderiv ℝ θ A v / w A) ∂matrixGaussianMeasure n)} := by
    intro q hq
    obtain ⟨F, hF, hFc, hv, hd⟩ := hq
    have heD : (∫ A, q.2 i A * (θ A / w A) ∂matrixGaussianMeasure n) =
        ∫ A, fderiv ℝ F A v * (θ A / w A) ∂matrixGaussianMeasure n := by
      apply integral_congr_ae
      filter_upwards [hd i] with A hA
      simp only [hA, v]
    have heV : (∫ A, q.1 A * (fderiv ℝ θ A v / w A) ∂matrixGaussianMeasure n) =
        ∫ A, F A * (fderiv ℝ θ A v / w A) ∂matrixGaussianMeasure n := by
      apply integral_congr_ae
      filter_upwards [hv] with A hA
      simp only [hA]
    change (∫ A, q.2 i A * (θ A / w A) ∂matrixGaussianMeasure n) =
      -(∫ A, q.1 A * (fderiv ℝ θ A v / w A) ∂matrixGaussianMeasure n)
    rw [heD, heV]
    refine (correspondenceMatrix_test_integral hn (fun A => fderiv ℝ F A v) θ).trans
      (Eq.trans ?_ (congrArg Neg.neg
        (correspondenceMatrix_test_integral hn F (fun A => fderiv ℝ θ A v))).symm)
    have hiD := (((hF.continuous_fderiv one_ne_zero).clm_apply
      (show Continuous (fun _ : MatrixRealSpace n => v) from continuous_const)).mul
        hθ.continuous).integrable_of_hasCompactSupport
          (μ := (volume : Measure (MatrixRealSpace n))) (hc.mul_left)
    have hiV := (hF.continuous.mul hD).integrable_of_hasCompactSupport
      (μ := (volume : Measure (MatrixRealSpace n))) hDc.mul_left
    have hiP := (hF.continuous.mul hθ.continuous).integrable_of_hasCompactSupport
      (μ := (volume : Measure (MatrixRealSpace n))) hc.mul_left
    exact (neg_eq_iff_eq_neg.mpr (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      hiD hiV hiP (fun A _ => hF.differentiable one_ne_zero A)
        (fun A _ => hθ.differentiable (by simp) A))).symm
  have ht : (∫ A, p.2 i A * (θ A / w A) ∂matrixGaussianMeasure n) =
      -(∫ A, p.1 A * (fderiv ℝ θ A v / w A) ∂matrixGaussianMeasure n) :=
    closure_minimal hsub hclosed hp
  exact (correspondenceMatrix_test_integral hn (p.2 i : MatrixRealSpace n → ℝ) θ).symm.trans
    (ht.trans (congrArg Neg.neg
      (correspondenceMatrix_test_integral hn (p.1 : MatrixRealSpace n → ℝ) _)))

/-- The simple-spectrum locus is open, from genuine local eigenvalue branches. -/
theorem correspondenceMatrix_simple_isOpen (n : ℕ) :
    IsOpen {A : MatrixRealSpace n | (Matrix.of A).charpoly.Separable} := by
  apply isOpen_iff_mem_nhds.mpr
  intro A hA
  obtain ⟨U, lab, ho, ha, hd, hr⟩ := matrixSimpleSpectrum_exists_smooth_local_labeling n A hA
  apply Filter.mem_of_superset (ho.mem_nhds ha)
  intro B hB
  exact matrix_injective_full_roots_separable n (Matrix.of B) (lab B) (hr B hB).1 (hr B hB).2

/-- A symmetric C¹ eigenvalue observable has a C¹ intrinsic lift throughout
simple spectrum, despite discontinuities of the chosen measurable labeling. -/
theorem correspondenceMatrix_lift_contDiffOn {n : ℕ}
    (F : Configuration n → ℝ) (hF : ContDiff ℝ 1 F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    ContDiffOn ℝ 1 (matrixSymmetricLift n F)
      {A : MatrixRealSpace n | (Matrix.of A).charpoly.Separable} := by
  apply (correspondenceMatrix_simple_isOpen n).contDiffOn_iff.mpr
  intro A hA
  obtain ⟨U, lab, ho, ha, hd, hr⟩ := matrixSimpleSpectrum_exists_smooth_local_labeling n A hA
  have heq : matrixSymmetricLift n F =ᶠ[nhds A] F ∘ lab := by
    filter_upwards [ho.mem_nhds ha] with B hB
    have hsB := matrix_injective_full_roots_separable n (Matrix.of B) (lab B) (hr B hB).1 (hr B
        hB).2
    have hcB := matrixMeasurableEigenvalues_spec n B hsB
    exact matrixSimpleSpectrum_symmetric_value n (Matrix.of B) hsB
      (matrixMeasurableEigenvalues n B) (lab B) hcB.1 (hr B hB).1 hcB.2 (hr B hB).2 F hsym
  exact (hF.contDiffAt.comp A ((hd.contDiffAt (ho.mem_nhds ha)).restrict_scalars
      ℝ)).congr_of_eventuallyEq heq

/-- Continuous-on-open-set functions can be paired with compact tests supported
inside that set, without a global continuity assumption. -/
theorem correspondenceMatrix_local_test_integrable {n : ℕ}
    (U : Set (MatrixRealSpace n)) (f θ : MatrixRealSpace n → ℝ)
    (hf : ContinuousOn f U) (hθ : Continuous θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ U) : Integrable (fun A => f A * θ A) volume := by
  apply ((hf.mono hs).mul hθ.continuousOn).integrableOn_compact hc
    |>.integrable_of_forall_notMem_eq_zero
  intro A hA
  simp [image_eq_zero_of_notMem_tsupport hA]

/-- On any open set where the representative is C¹, the closed matrix Sobolev
gradient agrees with its ordinary derivative. -/
theorem correspondenceMatrix_H1_local_derivative {n : ℕ} (hn : 0 < n)
    (p : MatrixGaussianSobolevPair n) (hp : p ∈ matrixGaussianH1Completion n)
    (f : MatrixRealSpace n → ℝ) (U : Set (MatrixRealSpace n)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U)
    (hv : (p.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] f)
    (i : MatrixRealIndex n) :
    ∀ᵐ A ∂(volume : Measure (MatrixRealSpace n)), A ∈ U →
      p.2 i A = fderiv ℝ f A (matrixRealCoordinates n (Pi.single i 1)) := by
  let v := matrixRealCoordinates n (Pi.single i 1)
  let g : MatrixRealSpace n → ℝ := p.2 i
  have hw₀ : Continuous (matrixGaussianDensityReal n) := by
    unfold matrixGaussianDensityReal
    simp only [matrixHSNormSq_eq_sum]
    fun_prop
  have hw : Continuous (fun A : MatrixRealSpace n => matrixGaussianDensityReal n A) := hw₀
  have hμ : matrixGaussianMeasure n = (volume : Measure (MatrixRealSpace n)).withDensity
      (fun A => ENNReal.ofReal (matrixGaussianDensityReal n A)) :=
    matrixGaussianMeasure_eq_withDensity hn
  have hgv : LocallyIntegrable g volume := by
    apply positive_density_integrable_locallyIntegrable volume _ g hw
      (fun A => matrixGaussianDensityReal_pos n hn A)
    rw [← hμ]
    exact (Lp.memLp (p.2 i)).integrable (by norm_num)
  have hac : (volume : Measure (MatrixRealSpace n)) ≪ matrixGaussianMeasure n := by
    rw [hμ]
    exact withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun A => (ENNReal.ofReal_pos.mpr (matrixGaussianDensityReal_pos n hn A)).ne')
  have hvV := hac.ae_eq hv
  have hD : ContinuousOn (fun A => fderiv ℝ f A v) U :=
    (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const
  -- Distributional uniqueness identifies the weak and classical derivatives locally.
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hgv.locallyIntegrableOn U).sub (hD.locallyIntegrableOn hU.measurableSet)) ?_
  · filter_upwards [hz] with A hA
    intro ha
    exact sub_eq_zero.mp (hA ha)
  intro θ hθ hc hs
  have hiG : Integrable (fun A => θ A * g A) volume := by
    simpa only [smul_eq_mul] using hgv.integrable_smul_left_of_hasCompactSupport hθ.continuous hc
  have hiD : Integrable (fun A => θ A * fderiv ℝ f A v) volume := by
    simpa only [mul_comm] using
      correspondenceMatrix_local_test_integrable U _ θ hD hθ.continuous hc hs
  have hiV : Integrable (fun A => f A * fderiv ℝ θ A v) volume :=
    correspondenceMatrix_local_test_integrable U _ _ hf.continuousOn
      ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply (𝕜 := ℝ) v) ((tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := θ) v).trans hs)
  have hiP := correspondenceMatrix_local_test_integrable U f θ hf.continuousOn hθ.continuous hc hs
  let : (volume : Measure (Fin 2 → ℝ)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi _
  let : (volume : Measure ℂ).IsAddHaarMeasure := by
    have h := Complex.volume_preserving_equiv_pi.symm Complex.measurableEquivPi
    rw [← h.map_eq]
    exact Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm.isAddHaarMeasure_map _
  let : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : (volume : Measure (MatrixRealSpace n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (by simpa only [mul_comm] using hiD) hiV hiP
    (fun A ha => (hf A (hs ha)).differentiableWithinAt one_ne_zero
      |>.differentiableAt (hU.mem_nhds (hs ha)))
    (fun A _ => hθ.differentiable (by simp) A)
  have hweak := correspondenceMatrix_H1_weak hn p hp i θ hθ hc
  have hvalue : (∫ A : MatrixRealSpace n, p.1 A * fderiv ℝ θ A v) =
      ∫ A, f A * fderiv ℝ θ A v := by
    apply integral_congr_ae
    filter_upwards [hvV] with A hA
    rw [hA]
  rw [hvalue] at hweak
  simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
  rw [integral_sub hiG hiD]
  have he : (∫ A : MatrixRealSpace n, θ A * g A) = ∫ A, g A * θ A := by
    apply integral_congr_ae
    exact ae_of_all _ fun A => mul_comm _ _
  rw [he]
  change (∫ A : MatrixRealSpace n, p.2 i A * θ A) - (∫ A, θ A * fderiv ℝ f A v) = 0
  rw [hweak]
  have heD : (∫ A : MatrixRealSpace n, θ A * fderiv ℝ f A v) =
      ∫ A, fderiv ℝ f A v * θ A := by
    apply integral_congr_ae
    exact ae_of_all _ fun A => mul_comm _ _
  rw [heD]
  linarith

/-- The previously separate derivative identification is derived from literal
H¹ membership and the C¹ symmetric eigenvalue observable. -/
theorem correspondenceMatrix_H1_derivative {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℝ) (hF : ContDiff ℝ 1 F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (p : MatrixGaussianSobolevPair n) (hp : p ∈ matrixGaussianH1Completion n)
    (hv : (p.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] matrixSymmetricLift n F) :
    ∀ i, (p.2 i : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
      (fun A => fderiv ℝ (matrixSymmetricLift n F) A (matrixRealCoordinates n (Pi.single i 1))) :=
          by
  intro i
  have hlocal := correspondenceMatrix_H1_local_derivative hn p hp (matrixSymmetricLift n F)
    _ (correspondenceMatrix_simple_isOpen n) (correspondenceMatrix_lift_contDiffOn F hF hsym) hv i
  have hac : matrixGaussianMeasure n ≪ (volume : Measure (MatrixRealSpace n)) := by
    rw [matrixGaussianMeasure_eq_withDensity hn]
    exact withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le hlocal, matrixGaussian_charpoly_separable_ae n] with A hA hs
  exact hA hs

/-- The literal matrix H¹ hypothesis yields both overlap inequalities of
Theorem 1.13, with no supplied derivative or overlap integrability bridge. -/
theorem correspondenceMatrix_H1_functional_inequalities {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℝ) (hF : ContDiff ℝ 1 F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (p : MatrixGaussianSobolevPair n) (hp : p ∈ matrixGaussianH1Completion n)
    (hv : (p.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] matrixSymmetricLift n F) :
    Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n) ∧
    Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) (ginibreMeasure n) ∧
    smoothGinibreVariance n F ≤
      (2 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n ∧
    squareEntropy (ginibreMeasure n) F ≤
      (4 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  -- Derivative identification and finite overlap energy follow from H¹ membership.
  have hd := correspondenceMatrix_H1_derivative hn F hF hsym p hp hv
  have hdF := hF.differentiable one_ne_zero
  obtain ⟨hlog, hlsi⟩ := matrixSpectralLift_H1_lsi hn F hdF hsym p hp hv hd
  refine ⟨matrixSpectralLift_H1_overlap_integrable F hdF hsym p hd, hlog, ?_, hlsi⟩
  exact matrixSpectralLift_H1_gaussian_poincare hn F hdF hsym p hp hv hd

/-- Membership of an ordinary function in Gaussian H¹ means that its value
represents the first component of an actual closed compact-gradient pair. -/
def MatrixGaussianH1Function (n : ℕ) (f : MatrixRealSpace n → ℝ) : Prop :=
  ∃ p : MatrixGaussianSobolevPair n, p ∈ matrixGaussianH1Completion n ∧
    (p.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] f

/-- Theorem 1.13 on the literal C¹ symmetric / matrix H¹ domain. Only the
paper's value-domain hypothesis is supplied; the derivative identification,
finite overlap energy and entropy integrability are conclusions. -/
theorem correspondenceMatrix_theorem_1_13 {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℝ) (hF : ContDiff ℝ 1 F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (hH1 : MatrixGaussianH1Function n (matrixSymmetricLift n F)) :
    Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n) ∧
    Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) (ginibreMeasure n) ∧
    smoothGinibreVariance n F ≤
      (2 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n ∧
    squareEntropy (ginibreMeasure n) F ≤
      (4 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  obtain ⟨p, hp, hv⟩ := hH1
  exact correspondenceMatrix_H1_functional_inequalities hn F hF hsym p hp hv

end
end GinibrePoincare
