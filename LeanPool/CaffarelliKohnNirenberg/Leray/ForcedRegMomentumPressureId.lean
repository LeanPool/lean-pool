/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumPressure
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Liouville
public import LeanPool.CaffarelliKohnNirenberg.Foundation.HomogeneousSobolev

/-!
# Identification of the quadratic pressure

The frequency pressure of a real tensor field satisfies the Laplacian identity
of the Riesz pressure; their difference is square integrable and weakly
harmonic, hence zero by Liouville's theorem. This identifies the pressure of
`lem:regularised-forced` with its frequency representation in the pressure
pairing of `eq:reg-momentum-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ComplexConjugate

noncomputable section

namespace CKN.Leray

/-- The gradient of a scalar test as a vector test. -/
@[expose]
def gradField (ψ : Vec3 → ℝ) : Vec3 → Vec3 := fun x k => CKN.spatialDeriv ψ k x

theorem gradField_contDiff {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (gradField ψ) :=
  contDiff_pi.2 fun k => CKN.contDiff_spatialDeriv_smooth hψ k

theorem gradField_hasCompactSupport {ψ : Vec3 → ℝ} (hψc : HasCompactSupport ψ) :
    HasCompactSupport (gradField ψ) :=
  (hψc.fderiv ℝ).comp_left (g := fun L : Vec3 →L[ℝ] ℝ => fun k => L (CKN.basisVec k))
    (by funext k; simp)

theorem fourier_testField_gradField {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (ξ : L2Vec3) :
    𝓕 (testField (gradField ψ)) ξ =
      ((2 * Real.pi * Complex.I) * 𝓕 (scalTestField ψ) ξ) • complexifyFrequency ξ := by
  ext k
  rw [fourier_testField_apply (gradField_contDiff hψ) (gradField_hasCompactSupport hψc)]
  change 𝓕 (scalTestField (CKN.spatialDeriv ψ k)) ξ = _
  rw [fourier_scalTest_spatialDeriv hψ hψc, PiLp.smul_apply, complexifyFrequency_apply,
    smul_eq_mul]
  ring

theorem integrable_forcedTensorComp_mul (T : RealTensorL2) (i j : Fin 3) {g : Vec3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    Integrable (fun x => forcedTensorComp T i j x * g x) := by
  have h1 := memLp_forcedTensorComp T i j
  rw [ofReal_two_eq] at h1
  exact h1.integrable_mul (hg.continuous.memLp_of_hasCompactSupport (p := 2) hgc)

/-- The Laplacian identity of the frequency pressure. -/
theorem integral_quadPressureTilde_laplacian (T : RealTensorL2) {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, quadPressureTilde T x * CKN.spatialLaplacian ψ x =
      -∑ i : Fin 3, ∑ j : Fin 3, ∫ x, forcedTensorComp T i j x * CKN.mixedSecond ψ i j x := by
  have h1 : ∫ x, quadPressureTilde T x * CKN.spatialLaplacian ψ x =
      ∫ ξ, (conj (pressureApplyFormula ξ ((Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
        (complexifyTensorL2 T) : L2Vec3 → ComplexTensor3) ξ)) *
        (-((forcedFourierLam ξ : ℝ) : ℂ) * 𝓕 (scalTestField ψ) ξ)).re := by
    rw [show (fun x => quadPressureTilde T x * CKN.spatialLaplacian ψ x) =
      fun x => CKN.spatialLaplacian ψ x * quadPressureTilde T x from
        funext fun x => mul_comm _ _,
      integral_mul_quadPressureTilde T _ (CKN.contDiff_spatialLaplacian_smooth hψ)
        (CKN.hasCompactSupport_spatialLaplacian hψc)]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_scalTest_laplacian hψ hψc]
  have h2 := integral_transport_eq_fourier T (gradField_contDiff hψ)
    (gradField_hasCompactSupport hψc)
  have h3 : ∫ ξ, (inner ℂ (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ
      ((Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (complexifyTensorL2 T) :
        L2Vec3 → ComplexTensor3) ξ))) (𝓕 (testField (gradField ψ)) ξ)).re =
      -∫ x, quadPressureTilde T x * CKN.spatialLaplacian ψ x := by
    rw [h1, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_testField_gradField hψ hψc, inner_divergence_gradient, Complex.neg_re]
  have hint : ∀ j i : Fin 3, Integrable
      (fun x => forcedTensorComp T j i x * CKN.mixedSecond ψ j i x) := fun j i =>
    integrable_forcedTensorComp_mul T j i
      (CKN.contDiff_spatialDeriv_smooth (CKN.contDiff_spatialDeriv_smooth hψ i) j)
      (CKN.hasCompactSupport_spatialDeriv (CKN.hasCompactSupport_spatialDeriv hψc i) j)
  have h4 : ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
      forcedTensorComp T j i x * CKN.spatialDeriv (fun y => gradField ψ y i) j x =
      ∑ j : Fin 3, ∑ i : Fin 3, ∫ x, forcedTensorComp T j i x * CKN.mixedSecond ψ j i x := by
    change ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
      forcedTensorComp T j i x * CKN.mixedSecond ψ j i x = _
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => hint j i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun i _ => hint j i]
  rw [h4, h3] at h2
  linarith only [h2]

/-- A square-integrable function has at most linear growth of its local
`L^{3/2}` norms on balls. -/
theorem lpNorm_threeHalves_ball_le {H : Vec3 → ℝ} (hH : MemLp H 2 volume) {ρ : ℝ} (hρ : 0 < ρ) :
    MemLp H (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (CKN.euclideanBall (0 : Vec3) ρ)) ∧
      lpNorm H (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (CKN.euclideanBall (0 : Vec3) ρ)) ≤
        lpNorm H 2 volume * (1 + ρ) := by
  set B : Set Vec3 := CKN.euclideanBall 0 ρ with hB
  have hfin : IsFiniteMeasure (volume.restrict B) := by
    rw [isFiniteMeasure_restrict]
    exact CKN.volume_euclideanBall_ne_top 0 hρ
  have hle : ENNReal.ofReal (3 / 2 : ℝ) ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hloc : MemLp H 2 (volume.restrict B) := hH.restrict B
  refine ⟨hloc.mono_exponent hle, ?_⟩
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hle hloc.aestronglyMeasurable
  have hexp : 1 / (ENNReal.ofReal (3 / 2 : ℝ)).toReal - 1 / (2 : ℝ≥0∞).toReal = 1 / 6 := by
    rw [ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  rw [hexp, Measure.restrict_apply_univ] at hcompare
  have hvol := CKN.euclideanBall_volume_rpow_third_le hρ
  have hvol6 : volume B ^ (1 / 6 : ℝ) ≤ ENNReal.ofReal (1 + ρ) := by
    have h1 : volume B ^ (1 / 6 : ℝ) = (volume B ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.rpow_mul]
      norm_num
    rw [h1]
    calc (volume B ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (2 * ρ) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hvol (by norm_num)
      _ = ENNReal.ofReal ((2 * ρ) ^ (1 / 2 : ℝ)) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
      _ ≤ ENNReal.ofReal (1 + ρ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Real.sqrt_eq_rpow]
          refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
          nlinarith only [sq_nonneg ρ]
  have hbound : eLpNorm H (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B) ≤
      eLpNorm H 2 volume * ENNReal.ofReal (1 + ρ) :=
    hcompare.trans (mul_le_mul' (eLpNorm_mono_measure _ Measure.restrict_le_self) hvol6)
  have hne : eLpNorm H 2 volume * ENNReal.ofReal (1 + ρ) ≠ ⊤ :=
    ENNReal.mul_ne_top hH.eLpNorm_ne_top ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono hne hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  exact h

/-- The Riesz pressure of a real tensor field is its frequency pressure. -/
theorem rieszPressure_ae_eq_quadPressureTilde (T : RealTensorL2) :
    rieszPressureSliceRepresentative 2 (by norm_num) (forcedPressureTensorLp T) =ᵐ[volume]
      quadPressureTilde T := by
  set q := rieszPressureSliceRepresentative 2 (by norm_num) (forcedPressureTensorLp T) with hq
  have hq2 : MemLp q 2 volume := memLp_rieszPressureSliceRepresentative_two _
  have ht2 := memLp_quadPressureTilde T
  have hH2 : MemLp (fun x => q x - quadPressureTilde T x) 2 volume := hq2.sub ht2
  have hweak : CKN.Foundation.Heat.WeaklyHarmonicOn Set.univ
      (fun x => q x - quadPressureTilde T x) := by
    intro ψ hψ hψc _
    rw [Measure.restrict_univ]
    have hΔ2 : MemLp (CKN.spatialLaplacian ψ) 2 volume :=
      (CKN.contDiff_spatialLaplacian_smooth hψ).continuous.memLp_of_hasCompactSupport
        (CKN.hasCompactSupport_spatialLaplacian hψc)
    have hi1 : Integrable (fun x => q x * CKN.spatialLaplacian ψ x) := hq2.integrable_mul hΔ2
    have hi2 : Integrable (fun x => quadPressureTilde T x * CKN.spatialLaplacian ψ x) :=
      ht2.integrable_mul hΔ2
    have e1 : ∫ x, q x * CKN.spatialLaplacian ψ x =
        -∑ i : Fin 3, ∑ j : Fin 3, ∫ x, forcedTensorComp T i j x * CKN.mixedSecond ψ i j x :=
      regularisedPressureSlice_riesz_laplacian_pairing (fun i j => forcedTensorComp T i j)
        (memLp_forcedTensorComp T) ψ hψ hψc
    have e2 := integral_quadPressureTilde_laplacian T hψ hψc
    calc ∫ x, (q x - quadPressureTilde T x) * CKN.spatialLaplacian ψ x
        = ∫ x, (q x * CKN.spatialLaplacian ψ x -
            quadPressureTilde T x * CKN.spatialLaplacian ψ x) := by
          congr 1; funext x; ring
      _ = 0 := by rw [integral_sub hi1 hi2, e1, e2, sub_self]
  have hzero := CKN.Foundation.Heat.weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth
    (C := lpNorm (fun x => q x - quadPressureTilde T x) 2 volume) lpNorm_nonneg
    (fun ρ hρ => (lpNorm_threeHalves_ball_le hH2 hρ).1) hweak
    (fun ρ hρ => (lpNorm_threeHalves_ball_le hH2 hρ).2)
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.1 hx

end CKN.Leray

end
