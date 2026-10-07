/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumScalar
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedPressure

/-!
# The transport pairing in frequency variables

The pairing `∑ⱼ ∑ᵢ ∫ Tⱼᵢ ∂ⱼgᵢ` of a real tensor field with the gradient of a
smooth compactly supported vector test is the real part of the frequency
pairing of `-2πi ξ·T̂` with the transformed test. This is the transport and
viscous-free pairing in the frequency form of `eq:reg-momentum-forced`, and the
tensor pairing of the pressure identity.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ComplexConjugate

noncomputable section

namespace CKN.Leray

/-- The continuous linear map placing a complex vector in the `j`th row of a
complex tensor. -/
@[expose]
def rowSlot (j : Fin 3) : ComplexVec3 →L[ℂ] ComplexTensor3 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ComplexVec3)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin 3 => ComplexVec3) j)

theorem rowSlot_apply (j : Fin 3) (v : ComplexVec3) (k : Fin 3) :
    rowSlot j v k = if k = j then v else 0 := by
  simp [rowSlot]

theorem inner_rowSlot (A : ComplexTensor3) (j : Fin 3) (v : ComplexVec3) :
    inner ℂ A (rowSlot j v) = inner ℂ (A j) v := by
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · simp [rowSlot_apply]
  · intro k _ hk
    simp [rowSlot_apply, hk]
  · simp

/-- The pairing with the row-slotted multiples `2πiξⱼ v` is the pairing of the
divergence source with `v`. -/
theorem inner_sum_rowSlot (ξ : L2Vec3) (A : ComplexTensor3) (v : ComplexVec3) :
    inner ℂ A (∑ j : Fin 3, rowSlot j (((2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)) • v)) =
      inner ℂ (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ A)) v := by
  rw [inner_sum, tensorDivergenceLinear_apply, inner_neg_left, inner_smul_left, sum_inner,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_rowSlot, inner_smul_right, inner_smul_left]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem hasFDerivAt_testField {g : Vec3 → Vec3} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : L2Vec3) :
    HasFDerivAt (testField g) (coordComplexify.comp ((fderiv ℝ g (WithLp.ofLp y)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap)) y :=
  coordComplexify.hasFDerivAt.comp y
    (((hg.differentiable (by simp)) (WithLp.ofLp y)).hasFDerivAt.comp y
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).hasFDerivAt)

theorem lineDeriv_testSchwartz_apply {g : Vec3 → Vec3} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (j : Fin 3) (y : L2Vec3) :
    (∂_{(WithLp.toLp 2 (CKN.basisVec j) : L2Vec3)} (testSchwartz g hg hgc)) y =
      coordComplexify (fderiv ℝ g (WithLp.ofLp y) (CKN.basisVec j)) := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (testField g) y _ = _
  rw [(hasFDerivAt_testField hg y).fderiv]
  rfl

theorem fourier_lineDeriv_testSchwartz {g : Vec3 → Vec3} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (j : Fin 3) (ξ : L2Vec3) :
    (𝓕 (∂_{(WithLp.toLp 2 (CKN.basisVec j) : L2Vec3)} (testSchwartz g hg hgc))) ξ =
      ((2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)) • 𝓕 (testField g) ξ := by
  have hgr : Function.HasTemperateGrowth fun x : L2Vec3 =>
      inner ℝ x (WithLp.toLp 2 (CKN.basisVec j) : L2Vec3) := by fun_prop
  rw [SchwartzMap.fourier_lineDerivOp_eq, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hgr,
    inner_toLp_basisVec, fourier_testSchwartz, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  rfl

/-- The tensor gradient test field of a vector test. -/
@[expose]
def gradTestSchwartz (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) : 𝓢(L2Vec3, ComplexTensor3) :=
  ∑ j : Fin 3, (∂_{(WithLp.toLp 2 (CKN.basisVec j) : L2Vec3)} (testSchwartz g hg hgc)).postcompCLM
    (rowSlot j)

theorem gradTestSchwartz_apply {g : Vec3 → Vec3} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (y : L2Vec3) :
    gradTestSchwartz g hg hgc y =
      ∑ j : Fin 3, rowSlot j (coordComplexify (fderiv ℝ g (WithLp.ofLp y) (CKN.basisVec j))) := by
  simp only [gradTestSchwartz, Fin.sum_univ_three, add_apply,
    SchwartzMap.postcompCLM_apply, lineDeriv_testSchwartz_apply]

theorem fourier_gradTestSchwartz {g : Vec3 → Vec3} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (ξ : L2Vec3) :
    (𝓕 (gradTestSchwartz g hg hgc)) ξ =
      ∑ j : Fin 3, rowSlot j (((2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)) •
        𝓕 (testField g) ξ) := by
  have hsum : 𝓕 (gradTestSchwartz g hg hgc) = ∑ j : Fin 3,
      (𝓕 (∂_{(WithLp.toLp 2 (CKN.basisVec j) : L2Vec3)} (testSchwartz g hg hgc))).postcompCLM
        (rowSlot j) := by
    unfold gradTestSchwartz
    rw [← SchwartzMap.fourierTransformCLM_apply ℂ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SchwartzMap.fourierTransformCLM_apply, fourier_postcompCLM]
  rw [hsum]
  simp only [Fin.sum_univ_three, add_apply, SchwartzMap.postcompCLM_apply,
    fourier_lineDeriv_testSchwartz]

theorem fderiv_apply_eq_spatialDeriv {g : Vec3 → Vec3} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) (x : Vec3) :
    fderiv ℝ g x (CKN.basisVec j) i = CKN.spatialDeriv (fun y => g y i) j x := by
  unfold CKN.spatialDeriv
  have h : HasFDerivAt (fun y => g y i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ g x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x
      ((hg.differentiable (by simp)) x).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem inner_complexifyTensor_gradTest (M : RealTensor3) (w : Fin 3 → Vec3) :
    (inner ℂ (complexifyTensorValue M) (∑ j : Fin 3, rowSlot j (coordComplexify (w j)))).re =
      ∑ j : Fin 3, ∑ i : Fin 3, M j i * w j i := by
  rw [inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_rowSlot, PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (inner ℂ ((M j i : ℝ) : ℂ) ((w j i : ℝ) : ℂ)).re = _
  simp [RCLike.inner_apply, mul_comm]

/-- The physical tensor pairing with the gradient test. -/
theorem re_inner_complexifyTensor_gradTestSchwartz (T : RealTensorL2) {g : Vec3 → Vec3}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    (inner ℂ (complexifyTensorL2 T) ((gradTestSchwartz g hg hgc).toLp 2)).re =
      ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
        forcedTensorComp T j i x * CKN.spatialDeriv (fun y => g y i) j x := by
  have hEmb : MeasurableEmbedding (WithLp.toLp 2 : Vec3 → L2Vec3) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.measurableEmbedding
  have h1 := vec3ToL2Vec3_measurePreserving.integral_comp hEmb
    (fun y : L2Vec3 => ∑ j : Fin 3, ∑ i : Fin 3, (T : L2Vec3 → RealTensor3) y j i *
      fderiv ℝ g (WithLp.ofLp y) (CKN.basisVec j) i)
  have h2 : ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
      forcedTensorComp T j i x * CKN.spatialDeriv (fun y => g y i) j x =
      ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3, (T : L2Vec3 → RealTensor3) (WithLp.toLp 2 x) j i *
        fderiv ℝ g (WithLp.ofLp (WithLp.toLp 2 x)) (CKN.basisVec j) i := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_apply_eq_spatialDeriv hg]
    rfl
  have hdef : complexifyTensorL2 T = complexifyTensorValue.compLpL 2 volume T := rfl
  rw [h2, h1, hdef, L2.inner_def, ← RCLike.re_to_complex,
    ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [complexifyTensorValue.coeFn_compLpL (p := 2) (μ := volume) T,
    (gradTestSchwartz g hg hgc).coeFn_toLp 2 (volume : Measure L2Vec3)] with y h3 h4
  rw [h3, h4, gradTestSchwartz_apply, RCLike.re_to_complex, inner_complexifyTensor_gradTest]

/-- The transport pairing in frequency variables. -/
theorem integral_transport_eq_fourier (T : RealTensorL2) {g : Vec3 → Vec3}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
        forcedTensorComp T j i x * CKN.spatialDeriv (fun y => g y i) j x =
      ∫ ξ, (inner ℂ (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ
        ((Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (complexifyTensorL2 T) :
          L2Vec3 → ComplexTensor3) ξ))) (𝓕 (testField g) ξ)).re := by
  set Θ := gradTestSchwartz g hg hgc with hΘ
  have hΘLp : Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (Θ.toLp 2) = (𝓕 Θ).toLp 2 :=
    SchwartzMap.toLp_fourier_eq Θ
  rw [← re_inner_complexifyTensor_gradTestSchwartz T hg hgc, ← hΘ,
    ← (Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3).inner_map_map, hΘLp, L2.inner_def,
    ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [(𝓕 Θ).coeFn_toLp 2 (volume : Measure L2Vec3)] with ξ hξ
  rw [hξ, hΘ, fourier_gradTestSchwartz, inner_sum_rowSlot]
  rfl

end CKN.Leray

end
