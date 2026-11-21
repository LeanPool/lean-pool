/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.AffineSubspaceSplitting
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # Genuine Gaussian law of the full affine eigen-row projection

Every scalar projection is the actual affine eigenfunction with the forced
center. Characteristic functions identify the whole subspace law with a
scaled standard Gaussian, without an assumed joint marginal law.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The orthogonal projection of a point centered at the Gibbs barycenter onto the affine eigen-
rows. -/
@[expose] noncomputable def affineRowProjection (V : E → ℝ) (ρ : ℝ) (x : E) : affineEigenRows V ρ :=
  (affineEigenRows V ρ).orthogonalProjectionOnto (x-affineSplittingCenter V)

/-- The standard Gaussian on the affine eigen-row space scaled by `1 / √ρ`. -/
@[expose] noncomputable def affineRowGaussian (V : E → ℝ) (ρ : ℝ) : Measure (affineEigenRows V ρ) :=
  (stdGaussian (affineEigenRows V ρ)).map (fun z => (Real.sqrt ρ)⁻¹ • z)

instance affineRowGaussian_isProbabilityMeasure (V : E → ℝ) (ρ : ℝ) :
    IsProbabilityMeasure (affineRowGaussian V ρ) := by
  unfold affineRowGaussian
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

theorem measurable_affineRowProjection (V : E → ℝ) (ρ : ℝ) : Measurable (affineRowProjection V ρ)
  := by
  exact ((affineEigenRows V ρ).orthogonalProjectionOnto.continuous.comp (continuous_id.sub
    continuous_const)).measurable

theorem affineRowProjection_hasLaw_gaussian
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) :
    HasLaw (affineRowProjection V ρ) (affineRowGaussian V ρ) (gibbsMeasure volume V) := by
  let := hp
  have hm := measurable_affineRowProjection V ρ
  refine ⟨hm.aemeasurable,?_⟩
  apply Measure.ext_of_charFun
  funext c
  have hid : (fun x : E => inner ℝ (affineRowProjection V ρ x) c) =
      fun x => inner ℝ (c:E) x+affineEigenConstant V ρ c := by
    funext x
    change inner ℝ ((affineEigenRows V ρ).orthogonalProjectionOnto (x-affineSplittingCenter V)) c =
      _
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,real_inner_comm,inner_sub_right,
      affineEigenConstant_eq_neg_inner_mean hV ρ hρ hHess hp]
    rfl
  have hg := affine_eigenfunction_hasLaw_gaussian_all V (hV.differentiable (by norm_num)) (c:E)
    (affineEigenConstant V ρ c) ρ hρ (affineEigenRows_eigenfunction V hρ c) hp
  have hvar : (((‖(c:E)‖^2/ρ).toNNReal : NNReal) : ℝ)=‖(c:E)‖^2/ρ :=
    Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) hρ.le)
  have hscale : ‖(Real.sqrt ρ)⁻¹ • c‖^2=‖(c:E)‖^2/ρ := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,inv_pow,Real.sq_sqrt hρ.le,Submodule.norm_coe]
    rw [div_eq_mul_inv]
    ring
  rw [charFun_map_eq_charFun_map_inner_one hm.aemeasurable,hid,hg.map_eq,charFun_gaussianReal]
  change _ = charFun ((stdGaussian (affineEigenRows V ρ)).map (fun z => (Real.sqrt ρ)⁻¹ • z)) c
  rw [charFun_map_smul (μ := stdGaussian (affineEigenRows V ρ)) ((Real.sqrt ρ)⁻¹)
    c,charFun_stdGaussian]
  simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_zero,zero_mul,one_pow,mul_one,zero_sub]
  rw [← Complex.ofReal_pow,hscale,hvar,neg_div]

end CutoffRigidity
