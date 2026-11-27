/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CoherentFrameFourier
public import LeanPool.VacuumBellSeparation.Gaussian.DensityWeylInversion

/-!
# The actual Husimi density recovers the actual Weyl characteristic

The square-root number-basis family has summable squared norms. Its
coherent-frame matrix elements have exactly those integral norms, so the
series/integral exchange is absolute. The result applies to every actual
positive trace-class operator and uses its complex density expectation.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped ComplexConjugate ComplexOrder

theorem coherentFrame_self_eq_rankOne {m : ℕ} (x : MultiModeOscillatorSpace m)
    (w : Fin m → ℂ) :
    inner ℂ (multiCoherentFrameCoordinate x w) (multiCoherentFrameCoordinate x w) =
      ((Real.pi : ℂ) ^ m)⁻¹ * inner ℂ x
        (rankOne ℂ (multiCoherentVector (WithLp.toLp 2 w))
          (multiCoherentVector (WithLp.toLp 2 w)) x) := by
  simp only [multiCoherentFrameCoordinate, RCLike.inner_apply', map_mul,
    inner_conj_symm, rankOne_apply, inner_smul_right]
  have h := coherentFrame_normalization_sq m
  calc
    _ = (conj (((Real.sqrt Real.pi : ℂ) ^ m)⁻¹) *
        ((Real.sqrt Real.pi : ℂ) ^ m)⁻¹) *
        (inner ℂ (multiCoherentVector (WithLp.toLp 2 w)) x *
          inner ℂ x (multiCoherentVector (WithLp.toLp 2 w))) := by ring
    _ = _ := by rw [h]

theorem multiCoherentPositiveDiagonal_complex {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : 0 ≤ A) (w : Fin m → ℂ) :
    (multiCoherentPositiveDiagonal A w : ℂ) =
      ((Real.pi : ℂ) ^ m)⁻¹ * inner ℂ (multiCoherentVector (WithLp.toLp 2 w))
        (A (multiCoherentVector (WithLp.toLp 2 w))) := by
  have hi := (Complex.nonneg_iff.mp
    ((nonneg_iff_isPositive.mp hA).inner_nonneg_right
      (multiCoherentVector (WithLp.toLp 2 w)))).2
  have hr : (((inner ℂ (multiCoherentVector (WithLp.toLp 2 w))
      (A (multiCoherentVector (WithLp.toLp 2 w)))).re : ℝ) : ℂ) =
      inner ℂ (multiCoherentVector (WithLp.toLp 2 w))
        (A (multiCoherentVector (WithLp.toLp 2 w))) := by
    apply Complex.ext
    · rfl
    · exact hi
  simp only [multiCoherentPositiveDiagonal, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_pow, hr]

theorem continuous_multiCoherentPositiveDiagonal {m : ℕ}
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :
    Continuous (multiCoherentPositiveDiagonal A) := by
  have hc := (continuous_multiCoherentVector m).comp (PiLp.continuous_toLp 2 _)
  unfold multiCoherentPositiveDiagonal
  exact continuous_const.mul
    (Complex.continuous_re.comp (hc.inner (𝕜 := ℂ) (A.continuous.comp hc)))

theorem integrable_multiCoherentPositiveDiagonal {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) : Integrable (multiCoherentPositiveDiagonal A) := by
  refine ⟨(continuous_multiCoherentPositiveDiagonal A).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun w => multiCoherentPositiveDiagonal_nonneg hA.1 w),
    ← positiveTrace_eq_lintegral_multiCoherentDiagonal hA.1]
  exact hA.2

theorem hasSum_sqrt_coherentFrame_self {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (w : Fin m → ℂ) :
    HasSum (fun k => inner ℂ
      (multiCoherentFrameCoordinate (CFC.sqrt A (multiModeNumberBasis m k)) w)
      (multiCoherentFrameCoordinate (CFC.sqrt A (multiModeNumberBasis m k)) w))
      (multiCoherentPositiveDiagonal A w : ℂ) := by
  have h := (summable_familyExpectation_terms
    (fun k => CFC.sqrt A (multiModeNumberBasis m k))
    (summable_sqrt_basis_norm_sq (multiModeNumberBasis m) hA)
    (rankOne ℂ (multiCoherentVector (WithLp.toLp 2 w))
      (multiCoherentVector (WithLp.toLp 2 w)))).hasSum.mul_left ((Real.pi : ℂ) ^ m)⁻¹
  change HasSum _ (((Real.pi : ℂ) ^ m)⁻¹ *
    densityExpectation (multiModeNumberBasis m) A
      (rankOne ℂ (multiCoherentVector (WithLp.toLp 2 w))
        (multiCoherentVector (WithLp.toLp 2 w)))) at h
  simpa only [← coherentFrame_self_eq_rankOne, densityExpectation_rankOne _ hA.1,
    ← multiCoherentPositiveDiagonal_complex hA.1] using h

theorem integrable_densityCoherentFourier {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (z : MultiModePhaseSpace m) :
    Integrable (fun w : Fin m → ℂ => coherentFourierPhase z (WithLp.toLp 2 w) *
      (multiCoherentPositiveDiagonal A w : ℂ)) := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).integrable_of_bilin_of_bdd_left
    (μ := (volume : Measure (Fin m → ℂ))) 1
    (continuous_coherentFourierPhase z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => (norm_coherentFourierPhase z _).le)
    (integrable_multiCoherentPositiveDiagonal hA).ofReal
  simpa only [ContinuousLinearMap.mul_apply'] using! h

/-- Literal Fourier transform of the actual normalized coherent diagonal.
The Gaussian factor is nonzero, so this determines the complex characteristic. -/
theorem integral_densityCoherentFourier {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (z : MultiModePhaseSpace m) :
    (∫ w : Fin m → ℂ, coherentFourierPhase z (WithLp.toLp 2 w) *
      (multiCoherentPositiveDiagonal A w : ℂ)) =
        weylVacuumWeight m (fun j => z j) *
          densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl z) := by
  let v (k : Fin m → ℕ) := CFC.sqrt A (multiModeNumberBasis m k)
  let F (k : Fin m → ℕ) (w : Fin m → ℂ) :=
    coherentFourierPhase z (WithLp.toLp 2 w) *
      inner ℂ (multiCoherentFrameCoordinate (v k) w) (multiCoherentFrameCoordinate (v k) w)
  have hnorm (k : Fin m → ℕ) : (∫ w : Fin m → ℂ, ‖F k w‖) = ‖v k‖ ^ 2 := by
    simp only [F, norm_mul, norm_coherentFourierPhase, one_mul,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      Complex.norm_of_nonneg (sq_nonneg _)]
    exact integral_multiCoherentFrameCoordinate_norm_sq (v k)
  have hs : Summable fun k => ∫ w : Fin m → ℂ, ‖F k w‖ := by
    simpa only [hnorm, v] using! summable_sqrt_basis_norm_sq (multiModeNumberBasis m) hA
  have h := hasSum_integral_of_summable_integral_norm
    (fun k => integrable_coherentFrameFourier_kernel z (v k) (v k)) hs
  have hpoint (w : Fin m → ℂ) : (∑' k, F k w) =
      coherentFourierPhase z (WithLp.toLp 2 w) * (multiCoherentPositiveDiagonal A w : ℂ) :=
    ((hasSum_sqrt_coherentFrame_self hA w).mul_left
      (coherentFourierPhase z (WithLp.toLp 2 w))).tsum_eq
  change HasSum (fun k => ∫ w : Fin m → ℂ, F k w) (∫ w : Fin m → ℂ, ∑' k, F k w) at h
  simp_rw [hpoint] at h
  rw [← h.tsum_eq]
  simp only [F, integral_coherentFrameFourier_kernel, tsum_mul_left]
  rfl

end VacuumBellSeparation.Gaussian
