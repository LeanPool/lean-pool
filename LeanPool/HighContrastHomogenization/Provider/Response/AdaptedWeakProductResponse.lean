/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedWeakProduct
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseOptimizer
public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedCutoffGradientField
public import LeanPool.HighContrastHomogenization.Provider.Response.AnnealedWeakQuantity
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.AECongruence

/-!
# High-contrast homogenization: Provider.Response.AdaptedWeakProductResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Weak-product control of the adapted response cutoff term

The reference gradient and flux defects are transported in their separate
metric slots.  Their reciprocal distortions are multiplied before the rounded
grid estimate is applied, while the cutoff coefficient retains its inverse
side-length gain.  This gives the samplewise majorants used by the annealed
primal and adjoint weak quantities.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem memVectorL2_matVecMul (A : Mat d) {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U (fun x ↦ matVecMul A (f x)) := by
  refine MemLp.of_le_mul (c := ‖matContinuousLinearMap A‖) hf ?_ ?_
  · simpa only [matContinuousLinearMap_apply] using
      (matContinuousLinearMap A).continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [matContinuousLinearMap_apply] using
      (matContinuousLinearMap A).le_opNorm (f x)

omit [NeZero d] in
private theorem blockDiag_apply (A B : Mat d) (X : BlockVec d) :
    blockMatVecMul (blockDiag A B) X =
      ((matVecMul A X.1, matVecMul B X.2) : BlockVec d) := by
  apply Prod.ext
  · change matVecMul A X.1 + matVecMul 0 X.2 = matVecMul A X.1
    rw [zero_matVecMul, add_zero]
  · change matVecMul 0 X.1 + matVecMul B X.2 = matVecMul B X.2
    rw [zero_matVecMul, zero_add]

omit [NeZero d] in
private theorem originCube_halfWeight_sq (t : ℤ) :
    (3 : ℝ) ^ (-t) *
        cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t) ^ 2 = 1 := by
  rw [cubeBesovScaleWeight, cubeScaleFactor_originCube]
  norm_num
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  exact inv_mul_cancel₀ (zpow_ne_zero t (by norm_num : (3 : ℝ) ≠ 0))

private theorem adaptedResponse_weakProduct_sample
    {l t : ℤ} {m0 : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l (roundedGrid l m0))
    (b : CoeffSpace d) (p r : Vec d) (center : BlockVec d)
    (hfinite :
      ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (t : ℝ))) *
        adaptedWeakSeminorm (roundedGrid l m0) t (1 / 2) (fun x ↦
          blockMatVecMul (blockDiag (matSqrt m0) (matSqrt m0)⁻¹)
            (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid) t b p r x -
              center)) ≠ ⊤) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let W := ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (t : ℝ))) *
      adaptedWeakSeminorm (roundedGrid l m0) t (1 / 2) (fun x ↦
        blockMatVecMul (blockDiag (matSqrt m0) (matSqrt m0)⁻¹)
          (diagonalWeakState hq t b p r x - center))
    let term := Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      adaptedPreYoungCutoff (roundedGrid l m0) hq t x * ((1 / 2 : ℝ) *
        vecDot
          ((centeredResponseOptimizer (adaptedDomain hq t) b p r).toH1.grad x -
            center.1)
          (matVecMul ((b.coeffOn (adaptedDomain hq t)).toCoeffField x)
            ((centeredResponseOptimizer
              (adaptedDomain hq t) b p r).toH1.grad x) - center.2)))
    ENNReal.ofReal |term| ≤
        ENNReal.ofReal
          (divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d *
            ((51 / 50 : ℝ) * (d : ℝ) ^ 2)) *
          ENNReal.ofReal (W.toReal ^ 2) ∧
      ENNReal.ofReal (W.toReal ^ 2) ≤ W ^ (2 : ℕ) := by
  let q := roundedGrid l m0
  let hq : q.PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  let S := matSqrt m0
  let F : Vec d → BlockVec d := fun x ↦
    diagonalWeakState hq t b p r x - center
  let W : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (t : ℝ))) *
    adaptedWeakSeminorm q t (1 / 2) (fun x ↦
      blockMatVecMul (blockDiag S S⁻¹) (F x))
  let A : ℝ := Real.sqrt
    (matrixFrobeniusNormSq (matTranspose q * S⁻¹))
  let B : ℝ := Real.sqrt (matrixFrobeniusNormSq (q⁻¹ * S))
  have hS : S.PosDef := posDef_matSqrt hm0
  obtain ⟨hstate₁, hstate₂⟩ := diagonalWeakState_memVectorL2 hq t b p r
  have hdom := Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t
  have hF₁ : MemVectorL2 (adaptedCell q t) (fun x ↦ matVecMul S (F x).1) := by
    apply memVectorL2_matVecMul S
    change MemVectorL2 (adaptedCell q t)
      (fun x ↦ (diagonalWeakState hq t b p r x).1 - center.1)
    exact memVectorL2_sub_const hdom hstate₁ center.1
  have hF₂ : MemVectorL2 (adaptedCell q t) (fun x ↦ matVecMul S⁻¹ (F x).2) := by
    apply memVectorL2_matVecMul S⁻¹
    change MemVectorL2 (adaptedCell q t)
      (fun x ↦ (diagonalWeakState hq t b p r x).2 - center.2)
    exact memVectorL2_sub_const hdom hstate₂ center.2
  have hmetric : (fun x ↦
      ((matVecMul S (F x).1, matVecMul S⁻¹ (F x).2) : BlockVec d)) =
      fun x ↦ blockMatVecMul (blockDiag S S⁻¹) (F x) := by
    funext x
    exact (blockDiag_apply S S⁻¹ (F x)).symm
  obtain ⟨aRef, haRef⟩ := exists_adaptedReferenceCoeffOn hq t b
  obtain ⟨hae₁, hae₂⟩ :=
    centeredResponseOptimizerDefects_affineAE hq t b haRef p r center.1 center.2
  have hae₁' :
      canonicalMaximizerGradientDefectOnCube (originCube d t) aRef
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
          (matVecMul (matTranspose q) center.1) =ᵐ[
        volume.restrict (cubeSet (originCube d t))]
        fun y ↦ matVecMul (matTranspose q) (F (matVecMul q y)).1 := by
    simpa only [q, hq, F, diagonalWeakState, diagonalWeakOptimizer,
      centeredResponseOptimizer, Prod.fst_sub] using hae₁
  have hae₂' :
      canonicalMaximizerFluxDefectOnCube (originCube d t) aRef
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
          (matVecMul q⁻¹ center.2) =ᵐ[
        volume.restrict (cubeSet (originCube d t))]
        fun y ↦ matVecMul q⁻¹ (F (matVecMul q y)).2 := by
    simpa only [q, hq, F, diagonalWeakState, diagonalWeakOptimizer,
      centeredResponseOptimizer, Prod.snd_sub] using hae₂
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hAfin : ENNReal.ofReal A * W ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simpa only [W, q, hq, S, F] using hfinite)
  have hBfin : ENNReal.ofReal B * W ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simpa only [W, q, hq, S, F] using hfinite)
  have hgrad : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2) N
          (canonicalMaximizerGradientDefectOnCube (originCube d t) aRef
            (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
            (matVecMul (matTranspose q) center.1)) ≤
        (ENNReal.ofReal A * W).toReal := by
    intro N
    apply (ENNReal.ofReal_le_iff_le_toReal hAfin).mp
    rw [cubeBesovNegativeVectorPartialSeminorm_eq_of_ae_eq_on_cubeSet
      (1 / 2) N hae₁']
    have h := ofReal_partialSeminorm_metricPullback_fst_le_separate
      hq hS t (1 / 2) N F hF₁ hF₂
    rw [hmetric] at h
    have hexp : -(1 / 2 * (t : ℝ)) = -(1 / 2 : ℝ) * (t : ℝ) := by ring
    rw [hexp] at h
    calc
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (t : ℝ))) *
          ENNReal.ofReal A *
            adaptedWeakSeminorm q t (1 / 2)
              (fun x ↦ blockMatVecMul (blockDiag S S⁻¹) (F x)) := h
      _ = ENNReal.ofReal A * W := by simp only [W]; ac_rfl
  have hflux : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2) N
          (canonicalMaximizerFluxDefectOnCube (originCube d t) aRef
            (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
            (matVecMul q⁻¹ center.2)) ≤
        (ENNReal.ofReal B * W).toReal := by
    intro N
    apply (ENNReal.ofReal_le_iff_le_toReal hBfin).mp
    rw [cubeBesovNegativeVectorPartialSeminorm_eq_of_ae_eq_on_cubeSet
      (1 / 2) N hae₂']
    have h := ofReal_partialSeminorm_metricPullback_snd_le_separate
      hq hS t (1 / 2) N F hF₁ hF₂
    rw [hmetric] at h
    have hexp : -(1 / 2 * (t : ℝ)) = -(1 / 2 : ℝ) * (t : ℝ) := by ring
    rw [hexp] at h
    calc
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (t : ℝ))) *
          ENNReal.ofReal B *
            adaptedWeakSeminorm q t (1 / 2)
              (fun x ↦ blockMatVecMul (blockDiag S S⁻¹) (F x)) := h
      _ = ENNReal.ofReal B * W := by simp only [W]; ac_rfl
  have hraw := abs_cutoffProductTermOnCube_le_divCurlWeakNormCoeff
    (originCube d t) aRef
    (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
    (matVecMul (matTranspose q) center.1) (matVecMul q⁻¹ center.2)
    (B := adaptedCutoffDerivativeCoeff d * (3 : ℝ) ^ (-2 * t))
    (Bone := adaptedCutoffDerivativeCoeff d * (3 : ℝ) ^ (-t))
    (gradWeak := (ENNReal.ofReal A * W).toReal)
    (fluxWeak := (ENNReal.ofReal B * W).toReal)
    (mul_nonneg (adaptedCutoffDerivativeCoeff_nonneg d) (by positivity))
    (adaptedPreYoungCutoff_pullback_smooth hq t)
    (adaptedPreYoungCutoff_pullback_hasCompactSupport hq t)
    (adaptedPreYoungCutoff_pullback_tsupport_subset_openCubeSet hq t)
    (memLp_top_scalarCutoffGradientField_adaptedPreYoungCutoff_pullback hq t _)
    (contDiff_scalarCutoffGradientField_adaptedPreYoungCutoff_pullback hq t)
    (scalarCutoffGradientField_adaptedPreYoungCutoff_pullback_fderiv_bound hq t _)
    (cubeLpNorm_infty_scalarCutoffGradientField_adaptedPreYoungCutoff_pullback_le
      hq t _)
    hgrad hflux
  rw [cutoffProductTermOnCube_affineResponseOptimizer hq t b haRef
    (adaptedPreYoungCutoff q hq t) p r center.1 center.2] at hraw
  have hcoeff := divCurlWeakNormCoeff_originCube_adaptedPreYoungCutoff_le d t
  have hAB := roundedGrid_metricFrobenius_product_le hgrid.1 hm0
  have hscale := originCube_halfWeight_sq (d := d) t
  have hAt : (ENNReal.ofReal A * W).toReal = A * W.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0]
  have hBt : (ENNReal.ofReal B * W).toReal = B * W.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0]
  have hprod0 : 0 ≤
      (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t) *
          (ENNReal.ofReal A * W).toReal) *
        (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t) *
          (ENNReal.ofReal B * W).toReal) :=
    mul_nonneg
      (mul_nonneg (cubeBesovScaleWeight_nonneg _ _)
        ENNReal.toReal_nonneg)
      (mul_nonneg (cubeBesovScaleWeight_nonneg _ _)
        ENNReal.toReal_nonneg)
  have hreal :
      |Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredResponseOptimizer (adaptedDomain hq t) b p r).toH1.grad x -
              center.1)
            (matVecMul ((b.coeffOn (adaptedDomain hq t)).toCoeffField x)
              ((centeredResponseOptimizer
                (adaptedDomain hq t) b p r).toH1.grad x) - center.2)))| ≤
        (divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d *
          ((51 / 50 : ℝ) * (d : ℝ) ^ 2)) * W.toReal ^ 2 := by
    calc
      _ ≤ divCurlWeakNormCoeff (originCube d t)
            (adaptedCutoffDerivativeCoeff d * (3 : ℝ) ^ (-2 * t))
            (adaptedCutoffDerivativeCoeff d * (3 : ℝ) ^ (-t)) *
          ((cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t) *
              (ENNReal.ofReal A * W).toReal) *
            (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t) *
              (ENNReal.ofReal B * W).toReal)) := hraw
      _ ≤ (divCurlDimensionCoeff d *
            (adaptedCutoffDerivativeCoeff d * (3 : ℝ) ^ (-t))) *
          ((cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t) *
              (ENNReal.ofReal A * W).toReal) *
            (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t) *
              (ENNReal.ofReal B * W).toReal)) :=
        mul_le_mul_of_nonneg_right hcoeff hprod0
      _ = (divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d) *
          (A * B) *
            ((3 : ℝ) ^ (-t) *
              cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t) ^ 2) *
            W.toReal ^ 2 := by rw [hAt, hBt]; ring
      _ = (divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d) *
          (A * B) * W.toReal ^ 2 := by rw [hscale, mul_one]
      _ ≤ (divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d) *
          ((51 / 50 : ℝ) * (d : ℝ) ^ 2) * W.toReal ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAB
            (mul_nonneg (divCurlDimensionCoeff_nonneg d)
              (adaptedCutoffDerivativeCoeff_nonneg d))) (sq_nonneg _)
      _ = _ := by ring
  constructor
  · exact (ENNReal.ofReal_le_ofReal hreal).trans_eq (by
      rw [ENNReal.ofReal_mul (mul_nonneg
        (mul_nonneg (divCurlDimensionCoeff_nonneg d)
          (adaptedCutoffDerivativeCoeff_nonneg d)) (by positivity))])
  · rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (by simpa only [W, q, hq, S, F] using hfinite)]

/-- The adapted cutoff product for one physical response sample is controlled
by the square of its normalized metric weak root.  The harmless leading one
keeps the dimension-only coefficient nonzero when the weak root is infinite. -/
theorem ofReal_abs_adaptedResponseCutoff_le_weakRoot_sq
    {l t : ℤ} {m0 : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l (roundedGrid l m0))
    (b : CoeffSpace d) (p r : Vec d) (center : BlockVec d) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let W := ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (t : ℝ))) *
      adaptedWeakSeminorm (roundedGrid l m0) t (1 / 2) (fun x ↦
        blockMatVecMul (blockDiag (matSqrt m0) (matSqrt m0)⁻¹)
          (diagonalWeakState hq t b p r x - center))
    let term := Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      adaptedPreYoungCutoff (roundedGrid l m0) hq t x * ((1 / 2 : ℝ) *
        vecDot
          ((centeredResponseOptimizer (adaptedDomain hq t) b p r).toH1.grad x -
            center.1)
          (matVecMul ((b.coeffOn (adaptedDomain hq t)).toCoeffField x)
            ((centeredResponseOptimizer
              (adaptedDomain hq t) b p r).toH1.grad x) - center.2)))
    ENNReal.ofReal |term| ≤
      ENNReal.ofReal
        (1 + divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d *
          ((51 / 50 : ℝ) * (d : ℝ) ^ 2)) * W ^ (2 : ℕ) := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let W := ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (t : ℝ))) *
    adaptedWeakSeminorm (roundedGrid l m0) t (1 / 2) (fun x ↦
      blockMatVecMul (blockDiag (matSqrt m0) (matSqrt m0)⁻¹)
        (diagonalWeakState hq t b p r x - center))
  have hC0 : 0 ≤ divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d *
      ((51 / 50 : ℝ) * (d : ℝ) ^ 2) :=
    mul_nonneg
      (mul_nonneg (divCurlDimensionCoeff_nonneg d)
        (adaptedCutoffDerivativeCoeff_nonneg d)) (by positivity)
  by_cases hW : W = ⊤
  · have hcoef : ENNReal.ofReal
        (1 + divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d *
          ((51 / 50 : ℝ) * (d : ℝ) ^ 2)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by linarith only [hC0])
    dsimp only
    change _ ≤ ENNReal.ofReal
      (1 + divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d *
        ((51 / 50 : ℝ) * (d : ℝ) ^ 2)) * W ^ (2 : ℕ)
    rw [hW, ENNReal.top_pow (by norm_num), ENNReal.mul_top hcoef]
    exact le_top
  · have hpair := adaptedResponse_weakProduct_sample hm0 hgrid b p r center hW
    dsimp only at hpair ⊢
    exact hpair.1.trans (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (by linarith only [hC0])) hpair.2)

end

end HCPolySupport.HighContrast.Response
