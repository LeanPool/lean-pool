/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumTransport

/-!
# The quadratic pressure in frequency variables

For a real tensor field `T`, the real part of the inverse transform of the
double-Riesz symbol applied to `T̂` satisfies the Laplacian identity of the
Riesz pressure of `T`. Both are square integrable, so their difference is a
square-integrable weakly harmonic function and vanishes by Liouville's
theorem: the Riesz pressure has the frequency representation used in the
pressure pairing of `eq:reg-momentum-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ComplexConjugate

noncomputable section

namespace CKN.Leray

theorem pressureApplyFormula_eq (ξ : L2Vec3) (F : ComplexTensor3) :
    pressureApplyFormula ξ F = -((inverseFrequencyNormSq ξ : ℝ) : ℂ) *
      inner ℂ (complexifyFrequency ξ) (tensorDivergenceLinear ξ F) := by
  unfold pressureApplyFormula inverseFrequencyNormSq
  by_cases hξ : ξ = 0
  · simp [hξ]
  · simp [hξ]

theorem inverseFrequencyNormSq_mul (ξ : L2Vec3) (hξ : ξ ≠ 0) :
    inverseFrequencyNormSq ξ * ‖ξ‖ ^ 2 = 1 := by
  unfold inverseFrequencyNormSq
  simp only [hξ, ↓reduceIte]
  have : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
  field_simp

theorem complexifyFrequency_apply (ξ : L2Vec3) (k : Fin 3) :
    complexifyFrequency ξ k = ((ξ k : ℝ) : ℂ) := rfl

theorem inner_complexifyFrequency_left (ξ : L2Vec3) (z : ComplexVec3) :
    inner ℂ (complexifyFrequency ξ) z = ∑ k : Fin 3, ((ξ k : ℝ) : ℂ) * z k := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [RCLike.inner_apply, complexifyFrequency_apply, mul_comm]

theorem norm_sq_eq_sum_coord (ξ : L2Vec3) : ‖ξ‖ ^ 2 = ∑ k : Fin 3, (ξ k) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

theorem inner_neg_divergence_frequency (ξ : L2Vec3) (F : ComplexTensor3) :
    inner ℂ (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ F)) (complexifyFrequency ξ) =
      (2 * Real.pi * Complex.I) *
        conj (inner ℂ (complexifyFrequency ξ) (tensorDivergenceLinear ξ F)) := by
  rw [inner_neg_left, inner_smul_left, ← inner_conj_symm (tensorDivergenceLinear ξ F)]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The divergence source against the Leray projection of a test vector:
`⟨-2πi ξ·F, ℙ̂z⟩ = ⟨-2πi ξ·F, z⟩ + conj(P̂F) · 2πi ⟨ξ, z⟩`. -/
theorem inner_divergence_leray (ξ : L2Vec3) (F : ComplexTensor3) (z : ComplexVec3) :
    inner ℂ (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ F)) (leraySymbol ξ z) =
      inner ℂ (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ F)) z +
        conj (pressureApplyFormula ξ F) *
          ((2 * Real.pi * Complex.I) * inner ℂ (complexifyFrequency ξ) z) := by
  rw [leraySymbol_apply_eq_formula, lerayApplyFormula, inner_sub_right, inner_smul_right,
    inner_neg_divergence_frequency, pressureApplyFormula_eq]
  simp only [map_mul, map_neg, Complex.conj_ofReal]
  ring

/-- The divergence source against a gradient test vector:
`⟨-2πi ξ·F, 2πi c ξ⟩ = -conj(P̂F) · (-λ c)`. -/
theorem inner_divergence_gradient (ξ : L2Vec3) (F : ComplexTensor3) (c : ℂ) :
    inner ℂ (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ F))
        (((2 * Real.pi * Complex.I) * c) • complexifyFrequency ξ) =
      -(conj (pressureApplyFormula ξ F) * (-((forcedFourierLam ξ : ℝ) : ℂ) * c)) := by
  by_cases hξ : ξ = 0
  · subst hξ
    have h0 : complexifyFrequency (0 : L2Vec3) = 0 := by
      ext k
      simp [complexifyFrequency_apply]
    simp [h0, pressureApplyFormula, forcedFourierLam]
  · have hι := inverseFrequencyNormSq_mul ξ hξ
    have hι' : ((inverseFrequencyNormSq ξ : ℝ) : ℂ) * ((‖ξ‖ : ℝ) : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, hι, Complex.ofReal_one]
    rw [inner_smul_right, inner_neg_divergence_frequency, pressureApplyFormula_eq]
    simp only [map_mul, map_neg, Complex.conj_ofReal, forcedFourierLam]
    push_cast
    linear_combination (4 * (Real.pi : ℂ) ^ 2 * c *
      conj (inner ℂ (complexifyFrequency ξ) (tensorDivergenceLinear ξ F))) * Complex.I_sq +
      (4 * (Real.pi : ℂ) ^ 2 * c *
        conj (inner ℂ (complexifyFrequency ξ) (tensorDivergenceLinear ξ F))) * hι'

/-- The real part of the inverse transform of the double-Riesz symbol of a
real tensor field, on Vec3. -/
@[expose]
def quadPressureTilde (T : RealTensorL2) : Vec3 → ℝ :=
  fun x => ((pressureL2Operator (complexifyTensorL2 T) : L2Vec3 → ℂ) (WithLp.toLp 2 x)).re

theorem fourier_pressureL2Operator (G : ComplexTensorL2) :
    (Lp.fourierTransformₗᵢ L2Vec3 ℂ (pressureL2Operator G) : L2Vec3 → ℂ) =ᵐ[volume]
      fun ξ => pressureApplyFormula ξ ((Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 G :
        L2Vec3 → ComplexTensor3) ξ) := by
  have h : Lp.fourierTransformₗᵢ L2Vec3 ℂ (pressureL2Operator G) =
      pressureFourierMultiplier (Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 G) := by
    unfold pressureL2Operator
    exact LinearIsometryEquiv.apply_symm_apply _ _
  rw [h]
  exact measurableFourierMultiplier_ae_eq _ _ _ _ _

theorem memLp_quadPressureTilde (T : RealTensorL2) : MemLp (quadPressureTilde T) 2 volume := by
  have h := (Lp.memLp (pressureL2Operator (complexifyTensorL2 T))).comp_measurePreserving
    vec3ToL2Vec3_measurePreserving
  exact h.re

/-- The pairing of the frequency pressure with a scalar test. -/
theorem integral_mul_quadPressureTilde (T : RealTensorL2) (χ : Vec3 → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    ∫ x, χ x * quadPressureTilde T x =
      ∫ ξ, (conj (pressureApplyFormula ξ ((Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
        (complexifyTensorL2 T) : L2Vec3 → ComplexTensor3) ξ)) * 𝓕 (scalTestField χ) ξ).re := by
  unfold quadPressureTilde
  rw [integral_scalTest_eq_fourier _ χ hχ hχc]
  refine integral_congr_ae ?_
  filter_upwards [fourier_pressureL2Operator (complexifyTensorL2 T)] with ξ hξ
  rw [hξ]

theorem integrable_fourier_integrand_scalTest {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (ξ : L2Vec3) :
    Integrable (fun v : L2Vec3 => 𝐞 (-⟪v, ξ⟫) • scalTestField χ v) := by
  rw [Real.fourierIntegral_convergent_iff]
  exact (scalTestField_contDiff hχ).continuous.integrable_of_hasCompactSupport
    (scalTestField_hasCompactSupport hχc)

/-- The transform of the Laplacian of a scalar test is `-λ` times the
transform of the test. -/
theorem fourier_scalTest_laplacian {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (ξ : L2Vec3) :
    𝓕 (scalTestField (CKN.spatialLaplacian ψ)) ξ =
      -((forcedFourierLam ξ : ℝ) : ℂ) * 𝓕 (scalTestField ψ) ξ := by
  have hd : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv (CKN.spatialDeriv ψ i) i) :=
    fun i => CKN.contDiff_spatialDeriv_smooth (CKN.contDiff_spatialDeriv_smooth hψ i) i
  have hdc : ∀ i : Fin 3, HasCompactSupport (CKN.spatialDeriv (CKN.spatialDeriv ψ i) i) :=
    fun i => CKN.hasCompactSupport_spatialDeriv (CKN.hasCompactSupport_spatialDeriv hψc i) i
  have hsum : 𝓕 (scalTestField (CKN.spatialLaplacian ψ)) ξ =
      ∑ i : Fin 3, 𝓕 (scalTestField (CKN.spatialDeriv (CKN.spatialDeriv ψ i) i)) ξ := by
    rw [Real.fourier_eq]
    simp_rw [Real.fourier_eq]
    rw [← integral_finsetSum _ fun i _ => integrable_fourier_integrand_scalTest (hd i) (hdc i) ξ]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [scalTestField, CKN.spatialLaplacian, Complex.ofReal_sum, Finset.smul_sum]
  rw [hsum]
  simp only [fourier_scalTest_spatialDeriv (CKN.contDiff_spatialDeriv_smooth hψ _)
    (CKN.hasCompactSupport_spatialDeriv hψc _), fourier_scalTest_spatialDeriv hψ hψc]
  rw [forcedFourierLam, norm_sq_eq_sum_coord, Fin.sum_univ_three, Fin.sum_univ_three]
  push_cast
  linear_combination (4 * (Real.pi : ℂ) ^ 2 *
    (((ξ 0 : ℝ) : ℂ) ^ 2 + ((ξ 1 : ℝ) : ℂ) ^ 2 + ((ξ 2 : ℝ) : ℂ) ^ 2) *
      𝓕 (scalTestField ψ) ξ) * Complex.I_sq

end CKN.Leray

end
