/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumTestTime
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian

/-!
# Scalar and vector spatial tests in frequency variables

Scalar smooth compactly supported tests are transported and complexified to
Schwartz functions; Plancherel expresses their integral against the real part
of a complex scalar `L²` field in frequency variables, and the transform turns
spatial derivatives into multiplication by `2πiξⱼ`. The components of the
transform of a vector test are the transforms of its components. These are the
scalar pairings of the pressure in `eq:reg-momentum-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ComplexConjugate

noncomputable section

namespace CKN.Leray

/-- The complexified scalar test on the Euclidean carrier. -/
@[expose]
def scalTestField (χ : Vec3 → ℝ) : L2Vec3 → ℂ := fun y => ((χ (WithLp.ofLp y) : ℝ) : ℂ)

theorem scalTestField_contDiff {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    ContDiff ℝ (⊤ : ℕ∞) (scalTestField χ) := by
  have he := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff (n := (⊤ : ℕ∞))
  exact Complex.ofRealCLM.contDiff.comp (hχ.comp he)

theorem scalTestField_hasCompactSupport {χ : Vec3 → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (scalTestField χ) := by
  have h1 := hχc.comp_homeomorph
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph
  exact h1.comp_left (g := Complex.ofRealCLM) (map_zero _)

/-- The Schwartz function of a smooth compactly supported scalar test. -/
@[expose]
def scalTestSchwartz (χ : Vec3 → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    𝓢(L2Vec3, ℂ) :=
  (scalTestField_hasCompactSupport hχc).toSchwartzMap (scalTestField_contDiff hχ)

/-- Plancherel for a scalar test against the real part of a complex scalar
field. -/
theorem integral_scalTest_eq_fourier (Z : Lp (α := L2Vec3) ℂ 2) (χ : Vec3 → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    ∫ x : Vec3, χ x * ((Z : L2Vec3 → ℂ) (WithLp.toLp 2 x)).re =
      ∫ ξ, (conj ((Lp.fourierTransformₗᵢ L2Vec3 ℂ Z : L2Vec3 → ℂ) ξ) *
        𝓕 (scalTestField χ) ξ).re := by
  set Ψ := scalTestSchwartz χ hχ hχc with hΨ
  have hΨLp : Lp.fourierTransformₗᵢ L2Vec3 ℂ (Ψ.toLp 2) = (𝓕 Ψ).toLp 2 :=
    SchwartzMap.toLp_fourier_eq Ψ
  have hEmb : MeasurableEmbedding (WithLp.toLp 2 : Vec3 → L2Vec3) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.measurableEmbedding
  have h1 : ∫ x : Vec3, χ x * ((Z : L2Vec3 → ℂ) (WithLp.toLp 2 x)).re =
      ∫ y : L2Vec3, χ (WithLp.ofLp y) * ((Z : L2Vec3 → ℂ) y).re :=
    vec3ToL2Vec3_measurePreserving.integral_comp hEmb
      (fun y : L2Vec3 => χ (WithLp.ofLp y) * ((Z : L2Vec3 → ℂ) y).re)
  have h2 : ∫ y : L2Vec3, χ (WithLp.ofLp y) * ((Z : L2Vec3 → ℂ) y).re =
      (inner ℂ Z (Ψ.toLp 2)).re := by
    rw [L2.inner_def, ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _)]
    refine integral_congr_ae ?_
    filter_upwards [Ψ.coeFn_toLp 2 (volume : Measure L2Vec3)] with y hy
    rw [hy]
    simp only [hΨ, scalTestSchwartz, HasCompactSupport.toSchwartzMap_toFun, scalTestField,
      RCLike.inner_apply, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h1, h2, ← (Lp.fourierTransformₗᵢ L2Vec3 ℂ).inner_map_map, hΨLp, L2.inner_def,
    ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [(𝓕 Ψ).coeFn_toLp 2 (volume : Measure L2Vec3)] with ξ hξ
  rw [hξ]
  simp only [RCLike.inner_apply, RCLike.re_to_complex]
  rw [mul_comm]
  rfl

/-- The transform turns a spatial derivative of a scalar test into
multiplication by `2πiξⱼ`. -/
theorem fourier_scalTest_spatialDeriv {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (j : Fin 3) (ξ : L2Vec3) :
    𝓕 (scalTestField (CKN.spatialDeriv χ j)) ξ =
      ((2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)) * 𝓕 (scalTestField χ) ξ := by
  set f := scalTestSchwartz χ hχ hχc with hf
  set m : L2Vec3 := WithLp.toLp 2 (CKN.basisVec j) with hm
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hS : ∂_{m} f = scalTestSchwartz (CKN.spatialDeriv χ j)
      (CKN.contDiff_spatialDeriv_smooth hχ j) (CKN.hasCompactSupport_spatialDeriv hχc j) := by
    refine SchwartzMap.ext fun y => ?_
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have hd : HasFDerivAt (fun y : L2Vec3 => ((χ (WithLp.ofLp y) : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((fderiv ℝ χ (WithLp.ofLp y)).comp e.toContinuousLinearMap)) y :=
      Complex.ofRealCLM.hasFDerivAt.comp y
        (((hχ.differentiable (by simp)) (WithLp.ofLp y)).hasFDerivAt.comp y e.hasFDerivAt)
    change fderiv ℝ (fun y : L2Vec3 => ((χ (WithLp.ofLp y) : ℝ) : ℂ)) y m = _
    rw [hd.fderiv]
    rfl
  have hg : Function.HasTemperateGrowth fun x : L2Vec3 => inner ℝ x m := by fun_prop
  have h1 : 𝓕 (scalTestField (CKN.spatialDeriv χ j)) ξ = (𝓕 (∂_{m} f)) ξ := by
    rw [hS]
    rfl
  have h2 : (𝓕 f) ξ = 𝓕 (scalTestField χ) ξ := rfl
  rw [h1, SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, hm, inner_toLp_basisVec, smul_eq_mul,
    Complex.real_smul, h2]
  ring

/-- The components of the transform of a vector test are the transforms of its
components. -/
theorem fourier_testField_apply {g : Vec3 → Vec3} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (ξ : L2Vec3) (k : Fin 3) :
    𝓕 (testField g) ξ k = 𝓕 (scalTestField (fun x => g x k)) ξ := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hint : Integrable (fun v : L2Vec3 => 𝐞 (-⟪v, ξ⟫) • testField g v) := by
    rw [Real.fourierIntegral_convergent_iff]
    exact (testField_contDiff hg).continuous.integrable_of_hasCompactSupport
      (testField_hasCompactSupport hgc)
  have h := (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 3 => ℂ) k).integral_comp_comm hint
  change (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 3 => ℂ) k)
    (∫ (v : L2Vec3), 𝐞 (-⟪v, ξ⟫) • testField g v) = _
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [PiLp.proj_apply, Circle.smul_def, PiLp.smul_apply, smul_eq_mul, scalTestField,
    testField, coordComplexify_apply]

end CKN.Leray

end
