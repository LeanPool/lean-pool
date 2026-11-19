/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianDbarVolumeDistributions.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarDistributionalClosure
public import LeanPool.GinibrePoincare.Analysis.GinibreIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! # Gaussian L² representatives as Lebesgue distributions
The strictly positive Gaussian density gives local Lebesgue integrability of
all Gaussian L² representatives, without any regularity assumption on them.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ComplexConjugate ContDiff
namespace GinibrePoincare
noncomputable section

/-- The real function `(n / π) ^ n * exp (-n ∑ i |z i|²)`, the Lebesgue density of the complex
Gaussian reference measure. -/
def gaussianLebesgueDensityReal (n : ℕ) (z : Configuration n) : ℝ :=
  ((n : ℝ) / Real.pi) ^ n * gaussianWeight n z

theorem gaussianLebesgueDensityReal_pos {n : ℕ} (hn : 0 < n)
    (z : Configuration n) : 0 < gaussianLebesgueDensityReal n z := by
  unfold gaussianLebesgueDensityReal
  exact mul_pos (pow_pos (div_pos (Nat.cast_pos.mpr hn) Real.pi_pos) _)
    (gaussianWeight_pos n z)

theorem contDiff_gaussianLebesgueDensityReal (n : ℕ) :
    ContDiff ℝ ∞ (gaussianLebesgueDensityReal n) := by
  unfold gaussianLebesgueDensityReal gaussianWeight
  exact contDiff_const.mul ((contDiff_const.mul contDiff_configurationNormSq).exp)

theorem complexGaussianMeasure_eq_real_withDensity {n : ℕ} (hn : 0 < n) :
    complexGaussianMeasure n = (volume : Measure (Configuration n)).withDensity
      (fun z => ENNReal.ofReal (gaussianLebesgueDensityReal n z)) := by
  rw [complexGaussianDensityIdentification n hn]
  rfl

theorem integral_complexGaussian_eq_density_volume {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℂ) :
    (∫ z, f z ∂complexGaussianMeasure n) =
      ∫ z, (gaussianLebesgueDensityReal n z : ℂ) * f z := by
  rw [complexGaussianMeasure_eq_real_withDensity hn,
    integral_withDensity_eq_integral_toReal_smul
      ((contDiff_gaussianLebesgueDensityReal n).continuous.measurable.ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gaussianLebesgueDensityReal_pos hn _).le,
    Complex.real_smul]

theorem integrable_complexGaussian_iff_density {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℂ) :
    Integrable f (complexGaussianMeasure n) ↔
      Integrable (fun z => (gaussianLebesgueDensityReal n z : ℂ) * f z) := by
  rw [complexGaussianMeasure_eq_real_withDensity hn, integrable_withDensity_iff_integrable_smul'
    ((contDiff_gaussianLebesgueDensityReal n).continuous.measurable.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gaussianLebesgueDensityReal_pos hn _).le,
    Complex.real_smul]

theorem gaussian_memLp_locallyIntegrable_volume {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℂ) (hf : MemLp f 2 (complexGaussianMeasure n)) :
    LocallyIntegrable f volume := by
  have hi : Integrable (fun z => (gaussianLebesgueDensityReal n z : ℂ) * f z) :=
    (integrable_complexGaussian_iff_density hn f).mp (hf.integrable (by norm_num))
  have hc : Continuous (fun z => ((gaussianLebesgueDensityReal n z : ℂ))⁻¹) := by
    apply (Complex.continuous_ofReal.comp (contDiff_gaussianLebesgueDensityReal n).continuous).inv₀
    intro z
    change (gaussianLebesgueDensityReal n z : ℂ) ≠ 0
    exact_mod_cast (gaussianLebesgueDensityReal_pos hn z).ne'
  have hl := hi.locallyIntegrable.mul_continuous hc
  apply hl.congr
  filter_upwards with z
  change (gaussianLebesgueDensityReal n z : ℂ) * f z *
    (gaussianLebesgueDensityReal n z : ℂ)⁻¹ = f z
  have hz : (gaussianLebesgueDensityReal n z : ℂ) ≠ 0 := by
    exact_mod_cast (gaussianLebesgueDensityReal_pos hn z).ne'
  field_simp

theorem dbarComponent_gaussianLebesgueDensityReal (n : ℕ) (j : Fin n)
    (z : Configuration n) :
    dbarComponent (fun w => (gaussianLebesgueDensityReal n w : ℂ)) j z =
      -(n : ℂ) * z j * gaussianLebesgueDensityReal n z := by
  have hd : DifferentiableAt ℝ (gaussianWeight n) z := by
    unfold gaussianWeight
    exact ((contDiff_const.mul contDiff_configurationNormSq).exp).differentiable
      (by simp) z
  have he : fderiv ℝ (fun w => (gaussianLebesgueDensityReal n w : ℂ)) z =
      Complex.ofRealCLM.comp
        ((((n : ℝ) / Real.pi) ^ n) • fderiv ℝ (gaussianWeight n) z) := by
    unfold gaussianLebesgueDensityReal
    rw [show (fun w : Configuration n =>
      ((((n : ℝ) / Real.pi) ^ n * gaussianWeight n w : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun w => ((n : ℝ) / Real.pi) ^ n * gaussianWeight n w) by rfl]
    rw [fderiv_comp _ Complex.ofRealCLM.differentiableAt (hd.const_mul _),
      Complex.ofRealCLM.fderiv, fderiv_const_mul hd]
  unfold dbarComponent
  rw [he]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    smul_eq_mul, Complex.ofRealCLM_apply]
  rw [fderiv_gaussianWeight_realCoordinate, fderiv_gaussianWeight_imaginaryCoordinate]
  unfold gaussianLebesgueDensityReal
  apply Complex.ext <;> simp <;> ring

theorem gaussianWeakDbar_integral_identity {n : ℕ}
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hu : IsGaussianWeakDbar n u D j)
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ z, θ z * D z ∂complexGaussianMeasure n) =
      ∫ z, u z * ((n : ℂ) * z j * θ z - dbarComponent θ j z)
        ∂complexGaussianMeasure n := by
  let φ := fun z => conj (θ z)
  have hφ : ContDiff ℝ 1 φ := Complex.conjCLE.contDiff.comp hθ
  have hcφ : HasCompactSupport φ := hc.comp_left (by simp)
  have he := hu φ hφ hcφ
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at he
  have ht := smoothCompactL2_coeFn φ hφ hcφ
  have ha := (gaussianDbarAdjointTest_memLp j φ hφ hcφ).coeFn_toLp
  calc
    _ = ∫ z, inner ℂ (smoothCompactL2 φ hφ hcφ z) (D z)
        ∂complexGaussianMeasure n := by
      apply integral_congr_ae
      filter_upwards [ht] with z hz
      rw [hz, RCLike.inner_apply]
      simp [φ]
      ring
    _ = _ := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ha] with z hz
      change (gaussianDbarAdjointTestL2 j φ hφ hcφ : Configuration n → ℂ) z = _ at hz
      rw [RCLike.inner_apply, hz]
      simp only [gaussianDbarAdjointTest, map_sub, map_mul, Complex.conj_natCast,
        starRingEnd_self_apply]
      have hcj : (fun w => conj (φ w)) = θ := by funext w; simp [φ]
      rw [hcj]
      simp only [φ, starRingEnd_self_apply]

/-- Ordinary Lebesgue distributional antiholomorphic derivative. Compact C¹
 tests are allowed; in particular the identity holds for every compact smooth test. -/
def IsGaussianVolumeDistributionalDbar (n : ℕ)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) : Prop :=
  LocallyIntegrable u volume ∧ LocallyIntegrable D volume ∧
    ∀ (θ : Configuration n → ℂ), ContDiff ℝ 1 θ → HasCompactSupport θ →
      (∫ z, θ z * D z) = -(∫ z, u z * dbarComponent θ j z)

theorem gaussianWeakDbar_volumeDistributional {n : ℕ} (hn : 0 < n)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hu : IsGaussianWeakDbar n u D j) :
    IsGaussianVolumeDistributionalDbar n u D j := by
  refine ⟨gaussian_memLp_locallyIntegrable_volume hn u (Lp.memLp u),
    gaussian_memLp_locallyIntegrable_volume hn D (Lp.memLp D), ?_⟩
  intro θ hθ hc
  let ρ : Configuration n → ℂ := fun z => gaussianLebesgueDensityReal n z
  have hρ : ContDiff ℝ 1 ρ := Complex.ofRealCLM.contDiff.comp
    ((contDiff_gaussianLebesgueDensityReal n).of_le (by simp))
  have hρ0 (z : Configuration n) : ρ z ≠ 0 := by
    dsimp [ρ]
    exact_mod_cast (gaussianLebesgueDensityReal_pos hn z).ne'
  let ψ : Configuration n → ℂ := fun z => θ z / ρ z
  have hψ : ContDiff ℝ 1 ψ := by
    have hri : ContDiff ℝ 1 (fun z => (gaussianLebesgueDensityReal n z)⁻¹) :=
      ((contDiff_gaussianLebesgueDensityReal n).of_le (by simp)).inv
        (fun z => (gaussianLebesgueDensityReal_pos hn z).ne')
    simpa only [ψ, ρ, div_eq_mul_inv, Function.comp_apply,
      Complex.ofRealCLM_apply, Complex.ofReal_inv] using
      hθ.mul (Complex.ofRealCLM.contDiff.comp hri)
  have hcψ : HasCompactSupport ψ := hc.mono (by
    intro z hz hzero
    apply hz
    simp only [ψ, hzero, zero_div])
  have heq : (fun z => ρ z * ψ z) = θ := by
    funext z
    dsimp [ψ]
    field_simp [hρ0 z]
  have hd (z : Configuration n) :
      ρ z * ((n : ℂ) * z j * ψ z - dbarComponent ψ j z) =
        -dbarComponent θ j z := by
    have he := congrFun heq z
    have hder := dbarComponent_mul (hρ.differentiable (by norm_num))
      (hψ.differentiable (by norm_num)) j z
    rw [heq] at hder
    change dbarComponent θ j z = _ at hder
    have hr := dbarComponent_gaussianLebesgueDensityReal n j z
    change dbarComponent ρ j z = -(n : ℂ) * z j * ρ z at hr
    rw [hr] at hder
    linear_combination hder
  have hi := gaussianWeakDbar_integral_identity u D j hu ψ hψ hcψ
  rw [integral_complexGaussian_eq_density_volume hn,
    integral_complexGaussian_eq_density_volume hn] at hi
  change (∫ z, ρ z * (ψ z * D z)) =
    ∫ z, ρ z * (u z * ((n : ℂ) * z j * ψ z - dbarComponent ψ j z)) at hi
  have hl : (fun z => ρ z * (ψ z * D z)) = (fun z => θ z * D z) := by
    funext z
    rw [← mul_assoc, congrFun heq z]
  have hr : (fun z => ρ z * (u z * ((n : ℂ) * z j * ψ z - dbarComponent ψ j z))) =
      (fun z => -(u z * dbarComponent θ j z)) := by
    funext z
    calc
      _ = u z * (ρ z * ((n : ℂ) * z j * ψ z - dbarComponent ψ j z)) := by ring
      _ = _ := by rw [hd]; ring
  rw [hl, hr, integral_neg] at hi
  exact hi

theorem gaussianWeakDbar_of_integral_identity {n : ℕ}
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hu : ∀ (θ : Configuration n → ℂ), ContDiff ℝ 1 θ → HasCompactSupport θ →
      (∫ z, θ z * D z ∂complexGaussianMeasure n) =
        ∫ z, u z * ((n : ℂ) * z j * θ z - dbarComponent θ j z)
          ∂complexGaussianMeasure n) : IsGaussianWeakDbar n u D j := by
  intro φ hφ hc
  have ht := smoothCompactL2_coeFn φ hφ hc
  have ha := (gaussianDbarAdjointTest_memLp j φ hφ hc).coeFn_toLp
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    _ = ∫ z, conj (φ z) * D z ∂complexGaussianMeasure n := by
      apply integral_congr_ae
      filter_upwards [ht] with z hz
      rw [RCLike.inner_apply, hz]
      ring
    _ = _ := hu (fun z => conj (φ z)) (Complex.conjCLE.contDiff.comp hφ)
      (hc.comp_left (by simp))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ha] with z hz
      change (gaussianDbarAdjointTestL2 j φ hφ hc : Configuration n → ℂ) z = _ at hz
      rw [RCLike.inner_apply, hz]
      simp only [gaussianDbarAdjointTest, map_sub, map_mul, Complex.conj_natCast,
        starRingEnd_self_apply]

theorem gaussianVolumeDistributionalDbar_weak {n : ℕ} (hn : 0 < n)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hu : IsGaussianVolumeDistributionalDbar n u D j) :
    IsGaussianWeakDbar n u D j := by
  apply gaussianWeakDbar_of_integral_identity
  intro θ hθ hc
  let ρ : Configuration n → ℂ := fun z => gaussianLebesgueDensityReal n z
  have hρ : ContDiff ℝ 1 ρ := Complex.ofRealCLM.contDiff.comp
    ((contDiff_gaussianLebesgueDensityReal n).of_le (by simp))
  have he := hu.2.2 (fun z => ρ z * θ z) (hρ.mul hθ) hc.mul_left
  rw [integral_complexGaussian_eq_density_volume hn,
    integral_complexGaussian_eq_density_volume hn]
  change (∫ z, ρ z * (θ z * D z)) =
    ∫ z, ρ z * (u z * ((n : ℂ) * z j * θ z - dbarComponent θ j z))
  have hd (z : Configuration n) : dbarComponent (fun z => ρ z * θ z) j z =
      -(ρ z * ((n : ℂ) * z j * θ z - dbarComponent θ j z)) := by
    rw [dbarComponent_mul (hρ.differentiable (by norm_num))
      (hθ.differentiable (by norm_num))]
    have hr := dbarComponent_gaussianLebesgueDensityReal n j z
    change dbarComponent ρ j z = -(n : ℂ) * z j * ρ z at hr
    rw [hr]
    ring
  calc
    _ = ∫ z, (ρ z * θ z) * D z := by
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ = _ := he
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with z
      rw [hd]
      ring

theorem gaussianWeakDbar_iff_volumeDistributional {n : ℕ} (hn : 0 < n)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) :
    IsGaussianWeakDbar n u D j ↔ IsGaussianVolumeDistributionalDbar n u D j :=
  ⟨gaussianWeakDbar_volumeDistributional hn u D j,
    gaussianVolumeDistributionalDbar_weak hn u D j⟩

end
end GinibrePoincare

