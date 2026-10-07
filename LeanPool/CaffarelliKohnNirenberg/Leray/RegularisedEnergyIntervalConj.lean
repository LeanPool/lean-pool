/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification

/-!
# Complex conjugation and the spatial Fourier transform

Coordinatewise complex conjugation of vector and tensor fields intertwines the
`L²` Fourier transform with the reflected conjugation `ĝ ↦ conj ĝ(-·)`. This
symmetry keeps the Fourier-side solution of the regularized mild equation
`eq:reg-mild` real-valued, which the energy equality of `thm:regularised`
uses.
-/

public section

open MeasureTheory Filter
open scoped ENNReal FourierTransform ComplexConjugate

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Coordinatewise complex conjugation of complex Euclidean vectors. -/
@[expose]
def complexVecConj : ComplexVec3 ≃ₗᵢ[ℝ] ComplexVec3 where
  toFun z := WithLp.toLp 2 (fun i => conj (z i))
  invFun z := WithLp.toLp 2 (fun i => conj (z i))
  map_add' z w := by
    apply PiLp.ext
    intro i
    simp
  map_smul' c z := by
    apply PiLp.ext
    intro i
    simp [Complex.real_smul]
  left_inv z := by
    apply PiLp.ext
    intro i
    simp
  right_inv z := by
    apply PiLp.ext
    intro i
    simp
  norm_map' z := by
    simp [PiLp.norm_eq_of_L2]

theorem complexVecConj_apply (z : ComplexVec3) (i : Fin 3) :
    complexVecConj z i = conj (z i) := rfl

theorem complexVecConj_involutive (z : ComplexVec3) :
    complexVecConj (complexVecConj z) = z :=
  complexVecConj.left_inv z

/-- Coordinatewise complex conjugation of complex Euclidean tensors. -/
@[expose]
def complexTensorConj : ComplexTensor3 ≃ₗᵢ[ℝ] ComplexTensor3 where
  toFun T := WithLp.toLp 2 (fun i => complexVecConj (T i))
  invFun T := WithLp.toLp 2 (fun i => complexVecConj (T i))
  map_add' S T := by
    apply PiLp.ext
    intro i
    simp
  map_smul' c T := by
    apply PiLp.ext
    intro i
    simp
  left_inv T := by
    apply PiLp.ext
    intro i
    simp [complexVecConj_involutive]
  right_inv T := by
    apply PiLp.ext
    intro i
    simp [complexVecConj_involutive]
  norm_map' T := by
    simp [PiLp.norm_eq_of_L2]

theorem complexTensorConj_apply (T : ComplexTensor3) (i : Fin 3) :
    complexTensorConj T i = complexVecConj (T i) := rfl

theorem complexVecConj_smul (c : ℂ) (z : ComplexVec3) :
    complexVecConj (c • z) = conj c • complexVecConj z := by
  apply PiLp.ext
  intro i
  simp [complexVecConj_apply]

theorem complexTensorConj_smul (c : ℂ) (T : ComplexTensor3) :
    complexTensorConj (c • T) = conj c • complexTensorConj T := by
  apply PiLp.ext
  intro i
  simp [complexTensorConj_apply, complexVecConj_smul]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The Fourier integral of a conjugated function is the conjugate of the
Fourier integral at the reflected frequency. -/
theorem fourier_comp_conj_apply [CompleteSpace F] (σ : F ≃ₗᵢ[ℝ] F)
    (hσ : ∀ (c : ℂ) (x : F), σ (c • x) = conj c • σ x)
    (f : L2Vec3 → F) (w : L2Vec3) :
    𝓕 (fun v => σ (f v)) w = σ (𝓕 f (-w)) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  refine Eq.trans ?_ (σ.toLinearIsometry.integral_comp_comm _)
  congr 1
  funext v
  change _ = σ _
  rw [Circle.smul_def, Circle.smul_def, hσ, inner_neg_right, neg_neg,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

variable (F) in
/-- Reflection `ξ ↦ -ξ` of the spatial variable, on `L²`. -/
@[expose]
def reflectLp : Lp (α := L2Vec3) F 2 →L[ℝ] Lp (α := L2Vec3) F 2 :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun ξ : L2Vec3 => -ξ)
    (Measure.measurePreserving_neg (volume : Measure L2Vec3))).toContinuousLinearMap

/-- Pointwise application of a real-linear isometry, on `L²`. -/
@[expose]
def conjLp (σ : F ≃ₗᵢ[ℝ] F) : Lp (α := L2Vec3) F 2 →L[ℝ] Lp (α := L2Vec3) F 2 :=
  ((σ.toContinuousLinearEquiv : F ≃L[ℝ] F) : F →L[ℝ] F).compLpL 2 volume

/-- The reflected conjugation `g ↦ σ(g(-·))` on `L²`. -/
@[expose]
def conjReflectLp (σ : F ≃ₗᵢ[ℝ] F) : Lp (α := L2Vec3) F 2 →L[ℝ] Lp (α := L2Vec3) F 2 :=
  (reflectLp F).comp (conjLp σ)

theorem conjLp_ae (σ : F ≃ₗᵢ[ℝ] F) (f : Lp (α := L2Vec3) F 2) :
    (conjLp σ f : L2Vec3 → F) =ᵐ[volume] fun ξ => σ (f ξ) :=
  ContinuousLinearMap.coeFn_compLpL _ f

theorem conjReflectLp_ae (σ : F ≃ₗᵢ[ℝ] F) (f : Lp (α := L2Vec3) F 2) :
    (conjReflectLp σ f : L2Vec3 → F) =ᵐ[volume] fun ξ => σ (f (-ξ)) := by
  have hneg := Measure.measurePreserving_neg (volume : Measure L2Vec3)
  have h1 := Lp.coeFn_compMeasurePreserving (conjLp σ f) hneg
  have h2 := hneg.quasiMeasurePreserving.ae (conjLp_ae σ f)
  filter_upwards [h1, h2] with ξ ha hb
  change (Lp.compMeasurePreserving (fun ξ : L2Vec3 => -ξ) hneg (conjLp σ f) :
    L2Vec3 → F) ξ = _
  rw [ha]
  exact hb

/-- The reflected conjugation is an involution. -/
theorem conjReflectLp_conjReflectLp (σ : F ≃ₗᵢ[ℝ] F) (hσσ : ∀ x, σ (σ x) = x)
    (f : Lp (α := L2Vec3) F 2) :
    conjReflectLp σ (conjReflectLp σ f) = f := by
  have hneg := Measure.measurePreserving_neg (volume : Measure L2Vec3)
  apply Lp.ext
  filter_upwards [conjReflectLp_ae σ (conjReflectLp σ f),
    hneg.quasiMeasurePreserving.ae (conjReflectLp_ae σ f)] with ξ h1 h2
  rw [h1, h2]
  simp only [neg_neg, hσσ]

/-- The reflected conjugation as a continuous real-linear involution. -/
@[expose]
def conjReflectEquiv (σ : F ≃ₗᵢ[ℝ] F) (hσσ : ∀ x, σ (σ x) = x) :
    Lp (α := L2Vec3) F 2 ≃L[ℝ] Lp (α := L2Vec3) F 2 :=
  ContinuousLinearEquiv.equivOfInverse (conjReflectLp σ) (conjReflectLp σ)
    (conjReflectLp_conjReflectLp σ hσσ) (conjReflectLp_conjReflectLp σ hσσ)

theorem conjReflectEquiv_apply (σ : F ≃ₗᵢ[ℝ] F) (hσσ : ∀ x, σ (σ x) = x)
    (f : Lp (α := L2Vec3) F 2) :
    conjReflectEquiv σ hσσ f = conjReflectLp σ f := rfl

/-- The `L²` Fourier transform of a conjugated field is the reflected
conjugate of its Fourier transform. -/
theorem fourierTransform_conjLp [CompleteSpace F] (σ : F ≃ₗᵢ[ℝ] F)
    (hσ : ∀ (c : ℂ) (x : F), σ (c • x) = conj c • σ x)
    (f : Lp (α := L2Vec3) F 2) :
    Lp.fourierTransformₗᵢ L2Vec3 F (conjLp σ f) =
      conjReflectLp σ (Lp.fourierTransformₗᵢ L2Vec3 F f) := by
  set ℱ := Lp.fourierTransformₗᵢ L2Vec3 F with hℱ
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ F 2 (volume : Measure L2Vec3)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  have hA : Continuous fun f : Lp (α := L2Vec3) F 2 => ℱ (conjLp σ f) :=
    ℱ.continuous.comp (conjLp σ).continuous
  have hB : Continuous fun f : Lp (α := L2Vec3) F 2 => conjReflectLp σ (ℱ f) :=
    (conjReflectLp σ).continuous.comp ℱ.continuous
  have hneg := Measure.measurePreserving_neg (volume : Measure L2Vec3)
  refine congrFun (hd.equalizer hA hB (funext fun g => ?_)) f
  simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply]
  set g' : SchwartzMap L2Vec3 F :=
    SchwartzMap.postcompCLM (𝕜 := ℝ) ((σ.toContinuousLinearEquiv : F ≃L[ℝ] F) : F →L[ℝ] F) g
    with hg'
  have hconj : conjLp σ (g.toLp 2) = g'.toLp 2 := by
    apply Lp.ext
    filter_upwards [conjLp_ae σ (g.toLp 2), g.coeFn_toLp 2 volume, g'.coeFn_toLp 2 volume]
      with ξ h1 h2 h3
    rw [h1, h2, h3, hg', SchwartzMap.postcompCLM_apply]
    rfl
  rw [hconj]
  change 𝓕 (g'.toLp 2) = conjReflectLp σ (𝓕 (g.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 g').coeFn_toLp 2 volume, conjReflectLp_ae σ ((𝓕 g).toLp 2),
    hneg.quasiMeasurePreserving.ae ((𝓕 g).coeFn_toLp 2 volume)] with ξ h1 h2 h3
  rw [h1, h2, h3, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have hfun : (g' : L2Vec3 → F) = fun v => σ (g v) := by
    funext v
    rw [hg', SchwartzMap.postcompCLM_apply]
    rfl
  rw [hfun]
  exact fourier_comp_conj_apply σ hσ g ξ

/-- The inverse `L²` Fourier transform of a reflected conjugate is the
conjugate of the inverse transform. -/
theorem conjLp_fourierTransform_symm [CompleteSpace F] (σ : F ≃ₗᵢ[ℝ] F)
    (hσ : ∀ (c : ℂ) (x : F), σ (c • x) = conj c • σ x)
    (g : Lp (α := L2Vec3) F 2) :
    conjLp σ ((Lp.fourierTransformₗᵢ L2Vec3 F).symm g) =
      (Lp.fourierTransformₗᵢ L2Vec3 F).symm (conjReflectLp σ g) := by
  apply (Lp.fourierTransformₗᵢ L2Vec3 F).injective
  rw [fourierTransform_conjLp σ hσ, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

end CKN.Leray

end
