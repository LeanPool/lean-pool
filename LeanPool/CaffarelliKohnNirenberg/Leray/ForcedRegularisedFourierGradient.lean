/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedFourierMild
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierPhysicalRange
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative

/-!
# Weak gradients from the Fourier transform

For a complex `L²` field `v` whose frequency gradient `2πi ξ ⊗ v̂` is square
integrable, the inverse transform of that tensor is the weak gradient of `v`.
Its real part is the weak gradient of the real part of `v`, and its squared
`L²` norm is the frequency dissipation `∫ 4π²|ξ|²|v̂|²`. This identifies the
dissipation of the energy identity of `lem:regularised-forced` with the
Dirichlet energy of the solution.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal FourierTransform LineDeriv SchwartzMap

noncomputable section

namespace CKN.Leray

/-- The frequency gradient `(2πi ξᵢ v̂ⱼ)ᵢⱼ` of a complex `L²` field. -/
@[expose]
def forcedFourierGradHat (v : ComplexVectorL2) (ξ : L2Vec3) : ComplexTensor3 :=
  WithLp.toLp 2 fun i => ((2 * Real.pi * Complex.I) * (ξ i : ℂ)) •
    (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 v : L2Vec3 → ComplexVec3) ξ

theorem norm_sq_forcedFourierGradHat (v : ComplexVectorL2) (ξ : L2Vec3) :
    ‖forcedFourierGradHat v ξ‖ ^ 2 = forcedFourierLam ξ *
      ‖(Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 v : L2Vec3 → ComplexVec3) ξ‖ ^ 2 := by
  rw [forcedFourierGradHat, PiLp.norm_sq_eq_of_L2]
  simp only [norm_smul, mul_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Complex.norm_ofNat, Real.norm_eq_abs, sq_abs, abs_of_pos Real.pi_pos]
  have hxi : ‖ξ‖ ^ 2 = ∑ i : Fin 3, ξ i ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Real.norm_eq_abs, sq_abs]
  rw [forcedFourierLam, hxi]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem measurable_forcedFourierGradHat (v : ComplexVectorL2) :
    Measurable (forcedFourierGradHat v) := by
  have hv : Measurable (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 v : L2Vec3 → ComplexVec3) :=
    (Lp.stronglyMeasurable _).measurable
  unfold forcedFourierGradHat
  fun_prop

/-- The inverse transform of the frequency gradient. -/
@[expose]
def forcedFourierGrad (v : ComplexVectorL2)
    (hv : MemLp (forcedFourierGradHat v) 2 volume) : ComplexTensorL2 :=
  (Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3).symm (hv.toLp (forcedFourierGradHat v))

theorem norm_sq_forcedFourierGrad (v : ComplexVectorL2)
    (hv : MemLp (forcedFourierGradHat v) 2 volume) :
    ‖forcedFourierGrad v hv‖ ^ 2 = ∫ ξ, forcedFourierLam ξ *
      ‖(Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 v : L2Vec3 → ComplexVec3) ξ‖ ^ 2 := by
  rw [forcedFourierGrad, LinearIsometryEquiv.norm_map, @norm_sq_eq_re_inner ℂ, L2.inner_def]
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _)]
  refine integral_congr_ae ?_
  filter_upwards [hv.coeFn_toLp] with ξ hξ
  rw [hξ, ← norm_sq_forcedFourierGradHat, inner_self_eq_norm_sq]

theorem inner_toLp_single_one (j : Fin 3) (w : ComplexVec3) :
    inner ℂ (WithLp.toLp 2 (Pi.single j (1 : ℂ)) : ComplexVec3) w = w j := by
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

/-- The continuous linear map placing a scalar in the `j`th slot of a complex
three-vector. -/
@[expose]
def complexVecSlot (j : Fin 3) : ℂ →L[ℂ] ComplexVec3 :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (WithLp.toLp 2 (Pi.single j (1 : ℂ)) : ComplexVec3)

/-- The continuous linear map placing a scalar in the `(i, j)` slot of a
complex three-by-three tensor. -/
@[expose]
def complexTensorSlot (i j : Fin 3) : ℂ →L[ℂ] ComplexTensor3 :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight
    (WithLp.toLp 2 (Pi.single i (WithLp.toLp 2 (Pi.single j (1 : ℂ)) : ComplexVec3)) :
      ComplexTensor3)

theorem inner_complexVecSlot (j : Fin 3) (a : ℂ) (w : ComplexVec3) :
    inner ℂ (complexVecSlot j a) w = (starRingEnd ℂ) a * w j := by
  simp only [complexVecSlot, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    inner_smul_left, inner_toLp_single_one]

theorem inner_complexTensorSlot (i j : Fin 3) (a : ℂ) (T : ComplexTensor3) :
    inner ℂ (complexTensorSlot i j a) T = (starRingEnd ℂ) a * T i j := by
  simp only [complexTensorSlot, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, inner_smul_left]
  congr 1
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, inner_toLp_single_one]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

/-- Line derivatives of Schwartz maps commute with real-linear postcomposition. -/
theorem schwartz_lineDerivOp_postcompCLM {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (f : 𝓢(L2Vec3, F)) (m : L2Vec3) :
    ∂_{m} (SchwartzMap.postcompCLM (𝕜 := ℝ) L f) =
      SchwartzMap.postcompCLM (𝕜 := ℝ) L (∂_{m} f) := by
  ext y
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.postcompCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hL := L.hasFDerivAt.comp y (f.differentiableAt.hasFDerivAt)
  change (fderiv ℝ (L ∘ f) y) m = _
  rw [hL.fderiv]
  rfl

theorem inner_toLp_basisVec (ξ : L2Vec3) (i : Fin 3) :
    inner ℝ ξ (WithLp.toLp 2 (CKN.basisVec i) : L2Vec3) = ξ i := by
  rw [PiLp.inner_apply]
  simp [CKN.basisVec, Pi.single_apply]

/-- The frequency identity behind the weak derivative: the pairing of a
differentiated slot vector with `w` is minus the pairing of the slot tensor
with the frequency gradient of `w`. -/
theorem inner_vecSlot_freqGrad (i j : Fin 3) (a : ℂ) (w : ComplexVec3) (ξ : L2Vec3) :
    inner ℂ (complexVecSlot j ((2 * Real.pi * Complex.I) * ((ξ i : ℝ) : ℂ) * a)) w =
      -inner ℂ (complexTensorSlot i j a)
        (WithLp.toLp 2 fun k => ((2 * Real.pi * Complex.I) * ((ξ k : ℝ) : ℂ)) • w :
          ComplexTensor3) := by
  rw [inner_complexVecSlot, inner_complexTensorSlot]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, PiLp.smul_apply,
    smul_eq_mul]
  ring

/-- The transform of a differentiated slot test vector. -/
theorem fourier_vecSlot_lineDeriv (i j : Fin 3) (φC : 𝓢(L2Vec3, ℂ)) (ξ : L2Vec3) :
    (𝓕 ((∂_{(WithLp.toLp 2 (CKN.basisVec i) : L2Vec3)} φC).postcompCLM (complexVecSlot j) :
        𝓢(L2Vec3, ComplexVec3)) : 𝓢(L2Vec3, ComplexVec3)) ξ =
      complexVecSlot j ((2 * Real.pi * Complex.I) * ((ξ i : ℝ) : ℂ) *
        (𝓕 φC : 𝓢(L2Vec3, ℂ)) ξ) := by
  rw [fourier_postcompCLM, SchwartzMap.postcompCLM_apply, SchwartzMap.fourier_lineDerivOp_eq]
  congr 1
  have hg : Function.HasTemperateGrowth fun x : L2Vec3 =>
      inner ℝ x (WithLp.toLp 2 (CKN.basisVec i) : L2Vec3) := by fun_prop
  rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg, inner_toLp_basisVec]
  simp only [smul_eq_mul, Complex.real_smul]
  ring

/-- The transform of a slot test tensor. -/
theorem fourier_tensorSlot (i j : Fin 3) (φC : 𝓢(L2Vec3, ℂ)) (ξ : L2Vec3) :
    (𝓕 (φC.postcompCLM (complexTensorSlot i j) : 𝓢(L2Vec3, ComplexTensor3)) :
        𝓢(L2Vec3, ComplexTensor3)) ξ = complexTensorSlot i j ((𝓕 φC : 𝓢(L2Vec3, ℂ)) ξ) := by
  rw [fourier_postcompCLM, SchwartzMap.postcompCLM_apply]

/-- Plancherel for a differentiated vector test field against a field with
square-integrable frequency gradient. -/
theorem forcedFourierGrad_inner_test (v : ComplexVectorL2)
    (hv : MemLp (forcedFourierGradHat v) 2 volume) (i j : Fin 3) (φC : 𝓢(L2Vec3, ℂ)) :
    inner ℂ ((((∂_{(WithLp.toLp 2 (CKN.basisVec i) : L2Vec3)} φC).postcompCLM
        (complexVecSlot j)) : 𝓢(L2Vec3, ComplexVec3)).toLp 2) v =
      -inner ℂ ((φC.postcompCLM (complexTensorSlot i j) : 𝓢(L2Vec3, ComplexTensor3)).toLp 2)
        (forcedFourierGrad v hv) := by
  set Ψ : 𝓢(L2Vec3, ComplexVec3) :=
    (∂_{(WithLp.toLp 2 (CKN.basisVec i) : L2Vec3)} φC).postcompCLM (complexVecSlot j) with hΨ
  set Θ : 𝓢(L2Vec3, ComplexTensor3) := φC.postcompCLM (complexTensorSlot i j) with hΘ
  have hΨLp : Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (Ψ.toLp 2) = (𝓕 Ψ).toLp 2 :=
    SchwartzMap.toLp_fourier_eq Ψ
  have hΘLp : Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (Θ.toLp 2) = (𝓕 Θ).toLp 2 :=
    SchwartzMap.toLp_fourier_eq Θ
  have hGhat : Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (forcedFourierGrad v hv) =
      hv.toLp (forcedFourierGradHat v) :=
    LinearIsometryEquiv.apply_symm_apply _ _
  rw [← (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).inner_map_map,
    ← (Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3).inner_map_map, hΨLp, hΘLp, hGhat,
    L2.inner_def, L2.inner_def, ← integral_neg]
  refine integral_congr_ae ?_
  have h3' : ((hv.toLp (forcedFourierGradHat v) : ComplexTensorL2) :
      L2Vec3 → ComplexTensor3) =ᵐ[volume] forcedFourierGradHat v := hv.coeFn_toLp
  filter_upwards [(𝓕 Ψ).coeFn_toLp 2, (𝓕 Θ).coeFn_toLp 2, h3'] with ξ h1 h2 h3
  rw [h1, h2, h3, hΨ, hΘ, fourier_vecSlot_lineDeriv, fourier_tensorSlot]
  exact inner_vecSlot_freqGrad i j ((𝓕 φC : 𝓢(L2Vec3, ℂ)) ξ) _ ξ

/-- The real part of the pairing of a slot test field with a complex vector
field is the integral against the real part of that component. -/
theorem re_inner_vecSlot_test (w : ComplexVectorL2) (j : Fin 3) (φL : 𝓢(L2Vec3, ℝ)) :
    (inner ℂ (((SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φL).postcompCLM
        (complexVecSlot j) : 𝓢(L2Vec3, ComplexVec3)).toLp 2) w).re =
      ∫ y : L2Vec3, φL y * ((w : L2Vec3 → ComplexVec3) y j).re := by
  let Ψ : 𝓢(L2Vec3, ComplexVec3) :=
    (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φL).postcompCLM (complexVecSlot j)
  have hpt : ∀ y, inner ℂ (Ψ y) ((w : L2Vec3 → ComplexVec3) y) =
      ((φL y : ℝ) : ℂ) * (w : L2Vec3 → ComplexVec3) y j := by
    intro y
    rw [SchwartzMap.postcompCLM_apply, inner_complexVecSlot, SchwartzMap.postcompCLM_apply,
      Complex.ofRealCLM_apply, Complex.conj_ofReal]
  have hint : Integrable (fun y : L2Vec3 =>
      ((φL y : ℝ) : ℂ) * (w : L2Vec3 → ComplexVec3) y j) := by
    refine (L2.integrable_inner (𝕜 := ℂ) (Ψ.toLp 2) w).congr ?_
    filter_upwards [Ψ.coeFn_toLp 2] with y hy
    rw [hy, hpt]
  change (inner ℂ (Ψ.toLp 2) w).re = _
  rw [L2.inner_def]
  have heq : ∫ y, inner ℂ ((Ψ.toLp 2 : L2Vec3 → ComplexVec3) y) ((w : L2Vec3 → ComplexVec3) y) =
      ∫ y : L2Vec3, ((φL y : ℝ) : ℂ) * (w : L2Vec3 → ComplexVec3) y j := by
    refine integral_congr_ae ?_
    filter_upwards [Ψ.coeFn_toLp 2] with y hy
    rw [hy, hpt]
  rw [heq, ← RCLike.re_to_complex, ← integral_re hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]

/-- The real part of the pairing of a slot test tensor with a complex tensor
field is the integral against the real part of that entry. -/
theorem re_inner_tensorSlot_test (G : ComplexTensorL2) (i j : Fin 3) (φL : 𝓢(L2Vec3, ℝ)) :
    (inner ℂ (((SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φL).postcompCLM
        (complexTensorSlot i j) : 𝓢(L2Vec3, ComplexTensor3)).toLp 2) G).re =
      ∫ y : L2Vec3, φL y * ((G : L2Vec3 → ComplexTensor3) y i j).re := by
  let Θ : 𝓢(L2Vec3, ComplexTensor3) :=
    (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φL).postcompCLM (complexTensorSlot i j)
  have hpt : ∀ y, inner ℂ (Θ y) ((G : L2Vec3 → ComplexTensor3) y) =
      ((φL y : ℝ) : ℂ) * (G : L2Vec3 → ComplexTensor3) y i j := by
    intro y
    rw [SchwartzMap.postcompCLM_apply, inner_complexTensorSlot, SchwartzMap.postcompCLM_apply,
      Complex.ofRealCLM_apply, Complex.conj_ofReal]
  have hint : Integrable (fun y : L2Vec3 =>
      ((φL y : ℝ) : ℂ) * (G : L2Vec3 → ComplexTensor3) y i j) := by
    refine (L2.integrable_inner (𝕜 := ℂ) (Θ.toLp 2) G).congr ?_
    filter_upwards [Θ.coeFn_toLp 2] with y hy
    rw [hy, hpt]
  change (inner ℂ (Θ.toLp 2) G).re = _
  rw [L2.inner_def]
  have heq : ∫ y, inner ℂ ((Θ.toLp 2 : L2Vec3 → ComplexTensor3) y)
      ((G : L2Vec3 → ComplexTensor3) y) =
      ∫ y : L2Vec3, ((φL y : ℝ) : ℂ) * (G : L2Vec3 → ComplexTensor3) y i j := by
    refine integral_congr_ae ?_
    filter_upwards [Θ.coeFn_toLp 2] with y hy
    rw [hy, hpt]
  rw [heq, ← RCLike.re_to_complex, ← integral_re hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]

/-- The real part of a complex `L²` field has, as weak partial derivatives,
the real parts of the inverse transform of its frequency gradient. -/
theorem forcedFourierGrad_hasWeakPartialDerivOn (v : ComplexVectorL2)
    (hv : MemLp (forcedFourierGradHat v) 2 volume) (i j : Fin 3) :
    CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) i
      (fun x => ((v : L2Vec3 → ComplexVec3) (WithLp.toLp 2 x) j).re)
      (fun x => ((forcedFourierGrad v hv : L2Vec3 → ComplexTensor3)
        (WithLp.toLp 2 x) i j).re) := by
  intro φ hφ hφc _
  let e : L2Vec3 ≃L[ℝ] Vec3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  let φS : 𝓢(Vec3, ℝ) := hφc.toSchwartzMap hφ
  let φL : 𝓢(L2Vec3, ℝ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e φS
  let m : L2Vec3 := WithLp.toLp 2 (CKN.basisVec i)
  have hdφL : ∀ y, (∂_{m} φL) y = fderiv ℝ φ (e y) (CKN.basisVec i) := by
    intro y
    rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rfl
  have hkey := forcedFourierGrad_inner_test v hv i j
    (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φL)
  rw [schwartz_lineDerivOp_postcompCLM] at hkey
  have hre := congrArg Complex.re hkey
  rw [Complex.neg_re, re_inner_vecSlot_test, re_inner_tensorSlot_test] at hre
  have hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    vec3ToL2Vec3_measurePreserving
  have h1 := hmp.integral_comp' (fun y : L2Vec3 =>
    ((∂_{m} φL) y) * ((v : L2Vec3 → ComplexVec3) y j).re)
  have h2 := hmp.integral_comp' (fun y : L2Vec3 =>
    (φL y) * ((forcedFourierGrad v hv : L2Vec3 → ComplexTensor3) y i j).re)
  simp only [MeasurableEquiv.coe_toLp] at h1 h2
  rw [← h1, ← h2] at hre
  have hφL : ∀ x : Vec3, φL (WithLp.toLp 2 x) = φ x := fun x => rfl
  have hdφL' : ∀ x : Vec3, (∂_{m} φL) (WithLp.toLp 2 x) = fderiv ℝ φ x (CKN.basisVec i) :=
    fun x => hdφL _
  simp only [hφL, hdφL'] at hre
  simp only [Measure.restrict_univ]
  calc ∫ x : Vec3, ((v : L2Vec3 → ComplexVec3) (WithLp.toLp 2 x) j).re *
        (fderiv ℝ φ x) (CKN.basisVec i)
      = ∫ x : Vec3, (fderiv ℝ φ x) (CKN.basisVec i) *
          ((v : L2Vec3 → ComplexVec3) (WithLp.toLp 2 x) j).re := by
        congr 1; funext x; ring
    _ = -∫ x : Vec3, φ x * ((forcedFourierGrad v hv : L2Vec3 → ComplexTensor3)
          (WithLp.toLp 2 x) i j).re := hre
    _ = -∫ x : Vec3, ((forcedFourierGrad v hv : L2Vec3 → ComplexTensor3)
          (WithLp.toLp 2 x) i j).re * φ x := by
        congr 2; funext x; ring

end CKN.Leray

end
