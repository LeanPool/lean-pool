/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineNormalization
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakSolution
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorNormalizedL2Bridge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicAffineDecay
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedReferenceConstantMatrix
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedSymmetricReferenceBounds
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseGeometry
public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneySquareWeights
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedAnalyticGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CubeVolume

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationHarmonicAffineDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine decay for the rounded constant reference

This file proves the deterministic constant-coefficient affine improvement
used at HC (5.66).  The rounded matrix itself is
the weak operator in the statement.  Its fixed `99/100`--`101/100` order
bounds are used only to make all geometric constants dimension-only.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

private theorem norm_matSqrt_eq_sqrt_specBound_roundDecay
    {d : ℕ} {A : Mat d} (hA : A.PosDef) :
    ‖matSqrt A‖ = Real.sqrt (specBound A) := by
  have hherm : (matSqrt A)ᴴ = matSqrt A :=
    (matSqrt_spec hA.posSemidef).1.isHermitian
  have hsq : ‖matSqrt A‖ ^ 2 = specBound A := by
    rw [pow_two, ← CStarRing.norm_self_mul_star,
      Matrix.star_eq_conjTranspose, hherm,
      (matSqrt_spec hA.posSemidef).2,
      specBound_eq_norm hA.posSemidef]
  symm
  exact (Real.sqrt_eq_iff_eq_sq (specBound_nonneg A) (norm_nonneg _)).mpr
    hsq.symm

private theorem roundedReference_matSqrt_norm_le_two
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    ‖matSqrt (geom.referenceMatrix abar hS)‖ ≤ 2 := by
  let A : Mat d := geom.referenceMatrix abar hS
  have hA : A.PosDef := by
    simpa only [A] using! geom.reference_posDef abar hS
  have horder : A ≤ (101 / 100 : ℝ) • (1 : Mat d) := by
    simpa only [A] using! geom.reference_upper abar hS
  have hnorm : ‖A‖ ≤ (101 / 100 : ℝ) := by
    have h := norm_le_norm_of_le hA.posSemidef
      (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 101 / 100)) horder
    simpa using h
  rw [norm_matSqrt_eq_sqrt_specBound_roundDecay hA,
    specBound_eq_norm hA.posSemidef]
  exact (Real.sqrt_le_iff).2 ⟨by norm_num, hnorm.trans (by norm_num)⟩

private theorem roundedReference_matSqrt_inv_norm_le_two
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    ‖(matSqrt (geom.referenceMatrix abar hS))⁻¹‖ ≤ 2 := by
  let A : Mat d := geom.referenceMatrix abar hS
  have hA : A.PosDef := by
    simpa only [A] using! geom.reference_posDef abar hS
  have hlower : (99 / 100 : ℝ) • (1 : Mat d) ≤ A := by
    simpa only [A] using! geom.reference_lower abar hS
  have hscalar : ((99 / 100 : ℝ) • (1 : Mat d)).PosDef :=
    Matrix.PosDef.one.smul (by norm_num)
  have hinv : A⁻¹ ≤ (100 / 99 : ℝ) • (1 : Mat d) := by
    have h := inv_le_inv_of_le hscalar hA hlower
    rw [inv_smul_of_isUnit (by norm_num : (99 / 100 : ℝ) ≠ 0)
      (by simp : IsUnit (1 : Mat d).det), inv_one] at h
    norm_num at h
    exact h
  have hnorm : ‖A⁻¹‖ ≤ (100 / 99 : ℝ) := by
    have h := norm_le_norm_of_le hA.inv.posSemidef
      (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 100 / 99)) hinv
    simpa using h
  rw [← matSqrt_inv hA,
    norm_matSqrt_eq_sqrt_specBound_roundDecay hA.inv,
    specBound_eq_norm hA.inv.posSemidef]
  exact (Real.sqrt_le_iff).2 ⟨by norm_num, hnorm.trans (by norm_num)⟩

private theorem two_mul_sqrt_dimension_le_three_pow_add_two
    (d : ℕ) [NeZero d] :
    (2 : ℝ) * Real.sqrt d ≤ (3 : ℝ) ^ (d + 2) := by
  have hd : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hsqrt : Real.sqrt d ≤ (d : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith only [hd]
  have hbern : 1 + (d : ℝ) * 2 ≤ (3 : ℝ) ^ d := by
    have h := one_add_mul_le_pow (a := (2 : ℝ)) (by norm_num) d
    norm_num at h
    exact h
  calc
    (2 : ℝ) * Real.sqrt d ≤ 2 * (d : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ ≤ (3 : ℝ) ^ d := by linarith only [hbern]
    _ ≤ (3 : ℝ) ^ (d + 2) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)

private theorem roundedPullback_sandwich
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) (k : ℤ) :
    let A := geom.referenceMatrix abar hS
    let S := matSqrt A
    let G := d + 2
    openCubeSet (originCube d (k - (G : ℤ))) ⊆
        matImage S⁻¹ (openCubeSet (originCube d k)) ∧
      matImage S⁻¹ (openCubeSet (originCube d k)) ⊆
        openCubeSet (originCube d (k + (G : ℤ))) := by
  dsimp only
  let A : Mat d := geom.referenceMatrix abar hS
  let S : Mat d := matSqrt A
  let G : ℕ := d + 2
  have hA : A.PosDef := by
    simpa only [A] using! geom.reference_posDef abar hS
  have hSpos : S.PosDef := by simpa only [S] using posDef_matSqrt hA
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hlarge : (2 : ℝ) * Real.sqrt d ≤ (3 : ℝ) ^ G := by
    simpa only [G] using two_mul_sqrt_dimension_le_three_pow_add_two d
  have hnormS : ‖S‖ * Real.sqrt d ≤ (3 : ℝ) ^ G := by
    exact (mul_le_mul_of_nonneg_right
      (by simpa only [S, A] using roundedReference_matSqrt_norm_le_two abar hS)
      (Real.sqrt_nonneg d)).trans hlarge
  have hnormInv : ‖S⁻¹‖ * Real.sqrt d ≤ (3 : ℝ) ^ G := by
    exact (mul_le_mul_of_nonneg_right
      (by simpa only [S, A] using roundedReference_matSqrt_inv_norm_le_two abar hS)
      (Real.sqrt_nonneg d)).trans hlarge
  have houter : adaptedCell S⁻¹ k ⊆ centeredCube d (k + (G : ℤ)) :=
    Selection.adaptedCell_subset_centeredCube_add hd hnormInv
  constructor
  · intro x hx
    have hsx : matVecMul S x ∈ centeredCube d k := by
      have himage : matVecMul S x ∈ adaptedCell S (k - (G : ℤ)) := by
        rw [adaptedCell_eq_matVecMul_image_openCubeSet]
        exact ⟨x, hx, rfl⟩
      have hcontained :=
        Selection.adaptedCell_subset_centeredCube_add hd hnormS himage
      simpa only [sub_add_cancel] using hcontained
    change x ∈ matImage S⁻¹ (openCubeSet (originCube d k))
    refine ⟨matVecMul S x, hsx, ?_⟩
    rw [matVecMul_mul, Matrix.nonsing_inv_mul S
      ((Matrix.isUnit_iff_isUnit_det S).mp hSpos.isUnit), matVecMul_one]
  · simpa only [adaptedCell_eq_matVecMul_image_openCubeSet] using! houter

@[expose]
public noncomputable def roundedAffineVolumeRatioBound (d : ℕ) : ℝ :=
  (Real.sqrt d * 2) ^ d * ((3 : ℝ) ^ (d + 2)) ^ d

private theorem roundedAffineVolumeRatioBound_nonneg (d : ℕ) :
    0 ≤ roundedAffineVolumeRatioBound d := by
  dsimp [roundedAffineVolumeRatioBound]
  positivity

private theorem roundedPullback_volume_ne_top
    {d : ℕ} (S : Mat d) (k : ℤ) :
    volume (matImage S (openCubeSet (originCube d k))) ≠ ∞ := by
  rw [volume_matImage]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (volume_openCubeSet_lt_top (originCube d k)).ne

private theorem originCube_scale_volume_ratio
    {d : ℕ} (k : ℤ) (G : ℕ) :
    cubeVolume (originCube d k) /
        cubeVolume (originCube d (k - (G : ℤ))) =
      ((3 : ℝ) ^ G) ^ d := by
  rw [cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale, ← div_pow]
  congr 1
  rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  change (3 : ℝ) ^ (k - (k - (G : ℤ))) = (3 : ℝ) ^ G
  rw [show k - (k - (G : ℤ)) = (G : ℤ) by omega, zpow_natCast]

private theorem originCube_outer_scale_volume_ratio
    {d : ℕ} (k : ℤ) (G : ℕ) :
    cubeVolume (originCube d (k + (G : ℤ))) /
        cubeVolume (originCube d k) =
      ((3 : ℝ) ^ G) ^ d := by
  rw [cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale, ← div_pow]
  congr 1
  rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  change (3 : ℝ) ^ (k + (G : ℤ) - k) = (3 : ℝ) ^ G
  rw [show k + (G : ℤ) - k = (G : ℤ) by omega, zpow_natCast]

private theorem roundedPullback_parent_volume_ratio_le
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) (k : ℤ) :
    let A := geom.referenceMatrix abar hS
    let S := matSqrt A
    let G := d + 2
    volume (matImage S⁻¹ (openCubeSet (originCube d k))) /
        volume (openCubeSet (originCube d (k - (G : ℤ)))) ≤
      ENNReal.ofReal (roundedAffineVolumeRatioBound d) := by
  dsimp only
  let A : Mat d := geom.referenceMatrix abar hS
  let S : Mat d := matSqrt A
  let G : ℕ := d + 2
  have hA : A.PosDef := by
    simpa only [A] using! geom.reference_posDef abar hS
  have hSpos : S.PosDef := by simpa only [S] using posDef_matSqrt hA
  have hden0 := volume_openCubeSet_ne_zero
    (originCube d (k - (G : ℤ)))
  have hratioTop :
      volume (matImage S⁻¹ (openCubeSet (originCube d k))) /
          volume (openCubeSet (originCube d (k - (G : ℤ)))) ≠ ∞ :=
    ENNReal.div_ne_top (roundedPullback_volume_ne_top S⁻¹ k) hden0
  apply (ENNReal.le_ofReal_iff_toReal_le hratioTop
    (roundedAffineVolumeRatioBound_nonneg d)).2
  rw [ENNReal.toReal_div, volume_matImage_toReal,
    volume_openCubeSet_toReal, volume_openCubeSet_toReal]
  have hdet : |(S⁻¹).det| ≤ (Real.sqrt d * 2) ^ d := by
    exact (Transport.abs_det_le_pow_norm S⁻¹).trans
      (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left
          (by simpa only [S, A] using
            roundedReference_matSqrt_inv_norm_le_two abar hS)
          (Real.sqrt_nonneg d)) d)
  dsimp only [roundedAffineVolumeRatioBound]
  calc
    |(S⁻¹).det| * cubeVolume (originCube d k) /
          cubeVolume (originCube d (k - (G : ℤ))) =
        |(S⁻¹).det| * ((3 : ℝ) ^ G) ^ d := by
      rw [mul_div_assoc, originCube_scale_volume_ratio]
    _ ≤ (Real.sqrt d * 2) ^ d * ((3 : ℝ) ^ G) ^ d :=
      mul_le_mul_of_nonneg_right hdet (by positivity)
    _ = (Real.sqrt d * 2) ^ d * ((3 : ℝ) ^ (d + 2)) ^ d := by
      rw [show G = d + 2 from rfl]

private theorem roundedPullback_child_volume_ratio_le
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) (k : ℤ) :
    let A := geom.referenceMatrix abar hS
    let S := matSqrt A
    let G := d + 2
    volume (openCubeSet (originCube d (k + (G : ℤ)))) /
        volume (matImage S⁻¹ (openCubeSet (originCube d k))) ≤
      ENNReal.ofReal (roundedAffineVolumeRatioBound d) := by
  dsimp only
  let A : Mat d := geom.referenceMatrix abar hS
  let S : Mat d := matSqrt A
  let G : ℕ := d + 2
  have hA : A.PosDef := by
    simpa only [A] using! geom.reference_posDef abar hS
  have hSpos : S.PosDef := by simpa only [S] using posDef_matSqrt hA
  have hdetUnit : IsUnit S.det :=
    (Matrix.isUnit_iff_isUnit_det S).mp hSpos.isUnit
  have hden0 :
      volume (matImage S⁻¹ (openCubeSet (originCube d k))) ≠ 0 :=
    by
      rw [volume_matImage]
      exact mul_ne_zero
        (ENNReal.ofReal_ne_zero_iff.mpr
          (abs_pos.mpr (Matrix.isUnit_nonsing_inv_det S hdetUnit).ne_zero))
        (volume_openCubeSet_ne_zero (originCube d k))
  have hratioTop :
      volume (openCubeSet (originCube d (k + (G : ℤ)))) /
          volume (matImage S⁻¹ (openCubeSet (originCube d k))) ≠ ∞ :=
    ENNReal.div_ne_top (volume_openCubeSet_lt_top _).ne hden0
  apply (ENNReal.le_ofReal_iff_toReal_le hratioTop
    (roundedAffineVolumeRatioBound_nonneg d)).2
  rw [ENNReal.toReal_div, volume_matImage_toReal,
    volume_openCubeSet_toReal, volume_openCubeSet_toReal]
  have hdetInv : |(S⁻¹).det| = |S.det|⁻¹ := by
    rw [Matrix.det_nonsing_inv]
    rw [Ring.inverse_eq_inv, abs_inv]
  have hdet : |S.det| ≤ (Real.sqrt d * 2) ^ d := by
    exact (Transport.abs_det_le_pow_norm S).trans
      (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left
          (by simpa only [S, A] using
            roundedReference_matSqrt_norm_le_two abar hS)
          (Real.sqrt_nonneg d)) d)
  dsimp only [roundedAffineVolumeRatioBound]
  have hdetPos : 0 < |S.det| := abs_pos.mpr hdetUnit.ne_zero
  have hvolPos : 0 < cubeVolume (originCube d k) := cubeVolume_pos _
  calc
    cubeVolume (originCube d (k + (G : ℤ))) /
          (|(S⁻¹).det| * cubeVolume (originCube d k)) =
        |S.det| * (cubeVolume (originCube d (k + (G : ℤ))) /
          cubeVolume (originCube d k)) := by
      rw [hdetInv]
      field_simp [hdetPos.ne', hvolPos.ne']
    _ = |S.det| * ((3 : ℝ) ^ G) ^ d := by
      rw [originCube_outer_scale_volume_ratio]
    _ ≤ (Real.sqrt d * 2) ^ d * ((3 : ℝ) ^ G) ^ d :=
      mul_le_mul_of_nonneg_right hdet (by positivity)
    _ = (Real.sqrt d * 2) ^ d * ((3 : ℝ) ^ (d + 2)) ^ d := by
      rw [show G = d + 2 from rfl]

@[expose]
public noncomputable def roundedAffineNormFactor (d : ℕ) : ℝ :=
  ((ENNReal.ofReal (roundedAffineVolumeRatioBound d)) ^ (1 / 2 : ℝ)).toReal

private theorem roundedAffineNormFactor_nonneg (d : ℕ) :
    0 ≤ roundedAffineNormFactor d :=
  ENNReal.toReal_nonneg

private theorem roundedHarmonicPullback_weakPoisson
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) (k : ℤ)
    (u : H1Function (openCubeSet (originCube d k)))
    (hu : IsWeakSolutionOn
      (constantCoeffField (geom.referenceMatrix abar hS))
      (openCubeSet (originCube d k)) u.grad) :
    let A := geom.referenceMatrix abar hS
    let S := matSqrt A
    let V := matImage S⁻¹ (openCubeSet (originCube d k))
    ∃ v : H1Function V,
      v.toFun = (fun y ↦ u.toFun (matVecMul S y)) ∧
      WeakPoissonEquationOn V v (fun _ ↦ 0) := by
  dsimp only
  let A : Mat d := geom.referenceMatrix abar hS
  let S : Mat d := matSqrt A
  let U : Set (Vec d) := openCubeSet (originCube d k)
  let V : Set (Vec d) := matImage S⁻¹ U
  have hA : A.PosDef := by
    simpa only [A] using! geom.reference_posDef abar hS
  have hAsymm : A.IsSymm := isSymm_of_isHermitian hA.isHermitian
  have hsymm : symmPart A = A := symmPart_eq_of_isSymm hAsymm
  have hsymmPos : (symmPart A).PosDef := by simpa only [hsymm] using hA
  have hSunit : IsUnit S.det := by
    simpa only [S, hsymm] using isUnit_det_matSqrt hsymmPos
  obtain ⟨v, hvfun, hvgrad⟩ :=
    exists_h1Function_affinePullback hSunit
      (measurableSet_openCubeSet (originCube d k)) u
  have htrans : matTranspose S = S := by
    simpa only [S] using! (isSymm_matSqrt A).eq
  have hpull := (isWeakSolutionOn_affinePullback_iff hSunit
    (measurableSet_openCubeSet (originCube d k))
    (constantCoeffField A) u.grad).mp (by simpa only [A, U] using hu)
  have hcoeff : affineCoefficient S hSunit (constantCoeffField A) =
      (fun _ ↦ (1 : Mat d)) := by
    funext y
    rw [affineCoefficient_apply]
    have htranspose : matTranspose S⁻¹ = S⁻¹ := by
      have hSinvHerm : (S⁻¹)ᴴ = S⁻¹ := by
        rw [Matrix.conjTranspose_nonsing_inv,
          show Sᴴ = S by simpa only [S] using!
            (matSqrt_spec hA.posSemidef).1.isHermitian]
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using! hSinvHerm
    rw [htranspose, show constantCoeffField A (matVecMul S y) = A from rfl,
      ← matSqrt_inv hA]
    exact matSqrt_inv_conj hA
  have hvsol : IsWeakSolutionOn (fun _ ↦ (1 : Mat d)) V v.grad := by
    rw [hvgrad]
    simpa only [V, U, htrans, hcoeff] using hpull
  refine ⟨v, by simpa only [S, U, V] using hvfun, ?_⟩
  intro phi hphi hcompact hsupport
  have hzero := (hvsol phi ⟨hphi, hcompact, hsupport⟩).2
  simpa only [matVecMul_one, vecDot_comm, zero_mul, integral_zero] using! hzero

private theorem volume_matImage_openCubeSet_ne_zero_roundDecay
    {d : ℕ} (L : Mat d) (hL : IsUnit L.det) (k : ℤ) :
    volume (matImage L (openCubeSet (originCube d k))) ≠ 0 := by
  rw [volume_matImage]
  exact mul_ne_zero
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr hL.ne_zero))
    (volume_openCubeSet_ne_zero (originCube d k))

private theorem real_le_roundedAffineNormFactor_of_normalizedL2
    {d : ℕ} {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hUzero : volume U ≠ 0) (hUtop : volume U ≠ ∞)
    (hVzero : volume V ≠ 0) (hVtop : volume V ≠ ∞)
    (hratio : volume V / volume U ≤
      ENNReal.ofReal (roundedAffineVolumeRatioBound d))
    (f : Vec d → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hUa : normalizedL2Norm U f = ENNReal.ofReal a)
    (hVb : normalizedL2Norm V f = ENNReal.ofReal b) :
    a ≤ roundedAffineNormFactor d * b := by
  have hrestrict := normalizedL2Norm_mono_set_le_volumeRatio
    hUV hUzero hUtop hVzero hVtop f
  have hfactor := ENNReal.rpow_le_rpow hratio
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have henn : ENNReal.ofReal a ≤
      (ENNReal.ofReal (roundedAffineVolumeRatioBound d)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal b := by
    rw [← hUa, ← hVb]
    exact hrestrict.trans (mul_le_mul_left hfactor _)
  have htop :
      (ENNReal.ofReal (roundedAffineVolumeRatioBound d)) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal b ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop henn
  simpa only [ENNReal.toReal_ofReal ha, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hb, roundedAffineNormFactor] using hreal

private theorem roundedPullback_parent_candidate_cubeLpNorm_le
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) (k : ℤ)
    (u v : Vec d → ℝ)
    (hv : v = fun y ↦ u (matVecMul
      (matSqrt (geom.referenceMatrix abar hS)) y))
    (c : ℝ) (e : Vec d)
    (hinnerMem : MemLp
      (fun y ↦ v y - (c + vecDot
        (matVecMul (matSqrt (geom.referenceMatrix abar hS)) e) y)) 2
      (normalizedCubeMeasure
        (originCube d (k - ((d + 2 : ℕ) : ℤ)))))
    (hparentMem : MemLp (fun x ↦ u x - (c + vecDot e x)) 2
      (normalizedCubeMeasure (originCube d k))) :
    cubeLpNorm (originCube d (k - ((d + 2 : ℕ) : ℤ))) 2
        (fun y ↦ v y - (c + vecDot
          (matVecMul (matSqrt (geom.referenceMatrix abar hS)) e) y)) ≤
      roundedAffineNormFactor d *
        cubeLpNorm (originCube d k) 2
          (fun x ↦ u x - (c + vecDot e x)) := by
  let A : Mat d := geom.referenceMatrix abar hS
  let S : Mat d := matSqrt A
  let G : ℕ := d + 2
  let Q : Set (Vec d) := openCubeSet (originCube d k)
  let P : Set (Vec d) := openCubeSet (originCube d (k - (G : ℤ)))
  let V : Set (Vec d) := matImage S⁻¹ Q
  let f : Vec d → ℝ := fun y ↦
    v y - (c + vecDot (matVecMul S e) y)
  let g : Vec d → ℝ := fun x ↦ u x - (c + vecDot e x)
  have hA : A.PosDef := by
    simpa only [A] using! geom.reference_posDef abar hS
  have hSunit : IsUnit S.det := by simpa only [S] using isUnit_det_matSqrt hA
  have hPV : P ⊆ V := by
    simpa only [P, V, Q, S, A, G] using
      (roundedPullback_sandwich abar hS k).1
  have hfun : f = fun y ↦ g (matVecMul S y) := by
    funext y
    dsimp only [f, g]
    rw [congrFun hv y]
    rw [show vecDot (matVecMul S e) y = vecDot e (matVecMul S y) by
      simpa only [S] using (vecDot_matSqrt_mulVec A e y).symm]
  have hVmeas : MeasurableSet V :=
    measurableSet_affinePullback hSunit (measurableSet_openCubeSet _)
  have hnormV : normalizedL2Norm V f =
      ENNReal.ofReal (cubeLpNorm (originCube d k) 2 g) := by
    rw [hfun]
    have hnorm := normalizedL2Norm_matImage hSunit hVmeas g
    rw [show matImage S V = Q by
      simpa only [V, Q] using matImage_matImage_inv hSunit Q] at hnorm
    calc
      normalizedL2Norm V (fun y ↦ g (matVecMul S y)) =
          normalizedL2Norm Q g := hnorm.symm
      _ = ENNReal.ofReal (cubeLpNorm (originCube d k) 2 g) := by
        simpa only [Q] using normalizedL2Norm_openCubeSet_eq_ofReal_cubeLpNorm
          (originCube d k) g (by simpa only [g] using hparentMem)
  apply real_le_roundedAffineNormFactor_of_normalizedL2 hPV
    (volume_openCubeSet_ne_zero _)
    (volume_openCubeSet_lt_top _).ne
    (volume_matImage_openCubeSet_ne_zero_roundDecay S⁻¹
      (by exact isUnit_det_matSqrt_inv hA) k)
    (roundedPullback_volume_ne_top S⁻¹ k)
    (by simpa only [V, P, Q, S, A, G] using
      roundedPullback_parent_volume_ratio_le abar hS k)
    f _ _ (cubeLpNorm_nonneg _ _ _) (cubeLpNorm_nonneg _ _ _)
  · simpa only [P, f, G, S, A] using
      normalizedL2Norm_openCubeSet_eq_ofReal_cubeLpNorm
        (originCube d (k - ((d + 2 : ℕ) : ℤ))) _ hinnerMem
  · exact hnormV

private theorem roundedPullback_child_candidate_cubeLpNorm_le
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) (r : ℤ)
    (u v : Vec d → ℝ)
    (hv : v = fun y ↦ u (matVecMul
      (matSqrt (geom.referenceMatrix abar hS)) y))
    (c : ℝ) (e : Vec d)
    (hphysicalMem : MemLp
      (fun x ↦ u x - (c + vecDot
        (matVecMul (matSqrt (geom.referenceMatrix abar hS))⁻¹ e) x)) 2
      (normalizedCubeMeasure (originCube d r)))
    (houterMem : MemLp (fun y ↦ v y - (c + vecDot e y)) 2
      (normalizedCubeMeasure
        (originCube d (r + ((d + 2 : ℕ) : ℤ))))) :
    cubeLpNorm (originCube d r) 2
        (fun x ↦ u x - (c + vecDot
          (matVecMul (matSqrt (geom.referenceMatrix abar hS))⁻¹ e) x)) ≤
      roundedAffineNormFactor d *
        cubeLpNorm (originCube d (r + ((d + 2 : ℕ) : ℤ))) 2
          (fun y ↦ v y - (c + vecDot e y)) := by
  let A : Mat d := geom.referenceMatrix abar hS
  let S : Mat d := matSqrt A
  let G : ℕ := d + 2
  let Q : Set (Vec d) := openCubeSet (originCube d r)
  let R : Set (Vec d) := openCubeSet (originCube d (r + (G : ℤ)))
  let V : Set (Vec d) := matImage S⁻¹ Q
  let f : Vec d → ℝ := fun y ↦ v y - (c + vecDot e y)
  let g : Vec d → ℝ := fun x ↦
    u x - (c + vecDot (matVecMul S⁻¹ e) x)
  have hA : A.PosDef := by
    simpa only [A] using! geom.reference_posDef abar hS
  have hSunit : IsUnit S.det := by simpa only [S] using isUnit_det_matSqrt hA
  have hVR : V ⊆ R := by
    simpa only [V, R, Q, S, A, G] using
      (roundedPullback_sandwich abar hS r).2
  have htrans : matTranspose S = S := by
    simpa only [S] using! (isSymm_matSqrt A).eq
  have hpair : ∀ y, vecDot (matVecMul S⁻¹ e) (matVecMul S y) =
      vecDot e y := by
    intro y
    calc
      vecDot (matVecMul S⁻¹ e) (matVecMul S y) =
          vecDot (matVecMul S y) (matVecMul S⁻¹ e) := vecDot_comm _ _
      _ = vecDot y (matVecMul (matTranspose S) (matVecMul S⁻¹ e)) :=
        (vecDot_matVecMul_transpose y (matVecMul S⁻¹ e) S).symm
      _ = vecDot e y := by
        rw [htrans, matVecMul_mul, Matrix.mul_nonsing_inv S hSunit,
          matVecMul_one, vecDot_comm]
  have hfun : f = fun y ↦ g (matVecMul S y) := by
    funext y
    dsimp only [f, g]
    rw [congrFun hv y, hpair]
  have hVmeas : MeasurableSet V :=
    measurableSet_affinePullback hSunit (measurableSet_openCubeSet _)
  have hnormV : normalizedL2Norm V f =
      ENNReal.ofReal (cubeLpNorm (originCube d r) 2 g) := by
    rw [hfun]
    have hnorm := normalizedL2Norm_matImage hSunit hVmeas g
    rw [show matImage S V = Q by
      simpa only [V, Q] using matImage_matImage_inv hSunit Q] at hnorm
    calc
      normalizedL2Norm V (fun y ↦ g (matVecMul S y)) =
          normalizedL2Norm Q g := hnorm.symm
      _ = ENNReal.ofReal (cubeLpNorm (originCube d r) 2 g) := by
        simpa only [Q] using normalizedL2Norm_openCubeSet_eq_ofReal_cubeLpNorm
          (originCube d r) g (by simpa only [g] using hphysicalMem)
  apply real_le_roundedAffineNormFactor_of_normalizedL2 hVR
    (volume_matImage_openCubeSet_ne_zero_roundDecay S⁻¹
      (by exact isUnit_det_matSqrt_inv hA) r)
    (roundedPullback_volume_ne_top S⁻¹ r)
    (volume_openCubeSet_ne_zero _)
    (volume_openCubeSet_lt_top _).ne
    (by simpa only [V, R, Q, S, A, G] using
      roundedPullback_child_volume_ratio_le abar hS r)
    f _ _ (cubeLpNorm_nonneg _ _ _) (cubeLpNorm_nonneg _ _ _)
  · exact hnormV
  · simpa only [R, f, G] using
      normalizedL2Norm_openCubeSet_eq_ofReal_cubeLpNorm
        (originCube d (r + ((d + 2 : ℕ) : ℤ))) _ houterMem

private theorem cubeBesovScaleWeight_one_originCube_sub_nat_roundDecay
    {d : ℕ} (k : ℤ) (N : ℕ) :
    cubeBesovScaleWeight 1 (originCube d (k - (N : ℤ))) =
      (3 : ℝ) ^ N * cubeBesovScaleWeight 1 (originCube d k) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.cast_succ]
      have hindex : k - (N : ℤ) - 1 = k - ((N : ℤ) + 1) := by ring
      rw [← hindex]
      have hone : cubeBesovScaleWeight 1
          (originCube d (k - (N : ℤ) - 1)) =
          3 * cubeBesovScaleWeight 1 (originCube d (k - (N : ℤ))) := by
        unfold cubeBesovScaleWeight
        change (((3 : ℝ) ^ (k - (N : ℤ) - 1)) ^ (-1 : ℝ)) =
          3 * (((3 : ℝ) ^ (k - (N : ℤ))) ^ (-1 : ℝ))
        rw [show k - (N : ℤ) - 1 = (k - (N : ℤ)) + (-1 : ℤ) by ring,
          zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num [Real.rpow_neg_one]
      rw [hone, ih]
      ring

/-- A solution of the genuinely rounded constant equation admits an affine
improvement with any prescribed positive contraction.  The proof is an exact
coordinate normalization; no identity residual is introduced. -/
theorem exists_printOrderRoundedReference_harmonic_normalized_affine_candidate_error_decay
    (d : ℕ) [NeZero d] (geom : RoundedGenerationAnalyticGeometry d)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (abar : Mat d) (hS : (symmPart abar).PosDef) (k : ℤ)
        (u : H1Function (openCubeSet (originCube d k))),
        IsWeakSolutionOn
            (constantCoeffField (geom.referenceMatrix abar hS))
            (openCubeSet (originCube d k)) u.grad →
          ∀ (c : ℝ) (e : Vec d), ∃ c' e',
            normalizedAffineCandidateError
                (originCube d (k - (N : ℤ))) u.toFun c' e' ≤
              theta * normalizedAffineCandidateError
                (originCube d k) u.toFun c e := by
  obtain ⟨depth, C₀, hC₀, hidentity⟩ :=
    CubeCalderonZygmund.exists_identity_harmonic_normalized_affine_candidate_error_decay_at_integer_rate
      d 1 (by norm_num)
  let G : ℕ := d + 2
  let K : ℝ := roundedAffineNormFactor d
  let P : ℝ := (3 : ℝ) ^ G * K
  let B : ℝ := 1 + C₀ * P ^ 2
  have hK : 0 ≤ K := by
    simpa only [K] using roundedAffineNormFactor_nonneg d
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hB : 0 < B := by
    dsimp [B]
    nlinarith only [hC₀, sq_nonneg P]
  have heps : 0 < theta / B := div_pos htheta hB
  obtain ⟨t, ht⟩ :=
    exists_pow_lt_of_lt_one heps (by norm_num : (1 : ℝ) / 3 < 1)
  let M : ℕ := depth + 2 * t + 2
  let N : ℕ := M + 2 * G
  have hN : 0 < N := by dsimp [N, M]; omega
  have hcoef : P * (C₀ * ((1 : ℝ) / 3) ^ t * P) ≤ theta := by
    have hCB : C₀ * P ^ 2 ≤ B := by
      dsimp [B]
      linarith only
    have hpow : 0 ≤ ((1 : ℝ) / 3) ^ t := by positivity
    calc
      P * (C₀ * ((1 : ℝ) / 3) ^ t * P) =
          (C₀ * P ^ 2) * ((1 : ℝ) / 3) ^ t := by ring
      _ ≤ B * ((1 : ℝ) / 3) ^ t :=
        mul_le_mul_of_nonneg_right hCB hpow
      _ ≤ B * (theta / B) := (mul_lt_mul_of_pos_left ht hB).le
      _ = theta := by field_simp [hB.ne']
  refine ⟨N, hN, ?_⟩
  intro abar hS k u hu c e
  let A : Mat d := geom.referenceMatrix abar hS
  let S : Mat d := matSqrt A
  let V : Set (Vec d) := matImage S⁻¹ (openCubeSet (originCube d k))
  let kp : ℤ := k - (G : ℤ)
  let r : ℤ := k - (N : ℤ)
  obtain ⟨v, hvfun, hvweak⟩ :=
    roundedHarmonicPullback_weakPoisson abar hS k u hu
  have hPV : openCubeSet (originCube d kp) ⊆ V := by
    simpa only [kp, V, S, A, G] using
      (roundedPullback_sandwich abar hS k).1
  let vP : H1Function (openCubeSet (originCube d kp)) :=
    v.restrict (isOpen_openCubeSet _) hPV
  have hvPfun : vP.toFun = fun y ↦ u.toFun (matVecMul S y) := by
    simpa only [vP, H1Function.restrict, S, V] using hvfun
  have hvPweak : WeakPoissonEquationOn
      (openCubeSet (originCube d kp)) vP (fun _ ↦ 0) := by
    simpa only [vP, H1Function.restrict] using
      hvweak.restrict (isOpen_openCubeSet _) hPV
  obtain ⟨c', e', hdecay⟩ := hidentity t kp vP hvPweak c (matVecMul S e)
  have hMform : depth + 2 * 1 * t + 2 = M := by dsimp [M]
  have hdecay' :
      normalizedAffineCandidateError
          (originCube d (kp - (M : ℤ))) vP.toFun c' e' ≤
        C₀ * ((1 : ℝ) / 3) ^ t *
          normalizedAffineCandidateError
            (originCube d kp) vP.toFun c (matVecMul S e) := by
    simpa only [hMform, show (2 * 1 - 1) * t = t by omega] using hdecay
  let ellU : H1Function (openCubeSet (originCube d k)) :=
    originCubeAffineH1LinearMap d k (c, e)
  let ellP : H1Function (openCubeSet (originCube d kp)) :=
    originCubeAffineH1LinearMap d kp (c, matVecMul S e)
  have hparentMem : MemLp (fun x ↦ u.toFun x - (c + vecDot e x)) 2
      (normalizedCubeMeasure (originCube d k)) := by
    have hraw := (u - ellU).memL2_normalizedCubeMeasure
    rw [H1Function.sub_toFun] at hraw
    rw [originCubeAffineH1LinearMap_toFun] at hraw
    exact hraw
  have hinnerMem : MemLp
      (fun y ↦ vP.toFun y - (c + vecDot (matVecMul S e) y)) 2
      (normalizedCubeMeasure (originCube d kp)) := by
    have hraw := (vP - ellP).memL2_normalizedCubeMeasure
    rw [H1Function.sub_toFun] at hraw
    rw [originCubeAffineH1LinearMap_toFun] at hraw
    exact hraw
  have hparentNorm := roundedPullback_parent_candidate_cubeLpNorm_le
    abar hS k u.toFun vP.toFun (by simpa only [S, A] using hvPfun)
    c e (by simpa only [kp, G] using hinnerMem) hparentMem
  have hweightParent : cubeBesovScaleWeight 1 (originCube d kp) =
      (3 : ℝ) ^ G * cubeBesovScaleWeight 1 (originCube d k) := by
    simpa only [kp] using
      cubeBesovScaleWeight_one_originCube_sub_nat_roundDecay (d := d) k G
  have hparentError :
      normalizedAffineCandidateError (originCube d kp) vP.toFun c
          (matVecMul S e) ≤
        P * normalizedAffineCandidateError (originCube d k) u.toFun c e := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance
    rw [hweightParent]
    calc
      ((3 : ℝ) ^ G * cubeBesovScaleWeight 1 (originCube d k)) *
          cubeLpNorm (originCube d kp) 2
            (fun y ↦ vP.toFun y - (c + vecDot (matVecMul S e) y)) ≤
        ((3 : ℝ) ^ G * cubeBesovScaleWeight 1 (originCube d k)) *
          (K * cubeLpNorm (originCube d k) 2
            (fun x ↦ u.toFun x - (c + vecDot e x))) := by
          exact mul_le_mul_of_nonneg_left (by simpa only [K, G, S, A] using hparentNorm)
            (mul_nonneg (by positivity) (cubeBesovScaleWeight_nonneg 1 _))
      _ = P * (cubeBesovScaleWeight 1 (originCube d k) *
          cubeLpNorm (originCube d k) 2
            (fun x ↦ u.toFun x - (c + vecDot e x))) := by
        dsimp [P]
        ring
  have hchildScale : r + (G : ℤ) = kp - (M : ℤ) := by
    dsimp [r, kp, N]
    omega
  have hchildParent : kp - (M : ℤ) ≤ kp := by omega
  let vR : H1Function (openCubeSet (originCube d (kp - (M : ℤ)))) :=
    vP.restrict (isOpen_openCubeSet _)
      (openCubeSet_originCube_subset_of_le hchildParent)
  let ellVR : H1Function
      (openCubeSet (originCube d (kp - (M : ℤ)))) :=
    originCubeAffineH1LinearMap d (kp - (M : ℤ)) (c', e')
  have houterMem : MemLp (fun y ↦ vP.toFun y - (c' + vecDot e' y)) 2
      (normalizedCubeMeasure (originCube d (kp - (M : ℤ)))) := by
    have hraw := (vR - ellVR).memL2_normalizedCubeMeasure
    rw [H1Function.sub_toFun] at hraw
    rw [originCubeAffineH1LinearMap_toFun] at hraw
    exact hraw
  have hrk : r ≤ k := by dsimp [r]; omega
  let uR : H1Function (openCubeSet (originCube d r)) :=
    u.restrict (isOpen_openCubeSet _)
      (openCubeSet_originCube_subset_of_le hrk)
  let ellUR : H1Function (openCubeSet (originCube d r)) :=
    originCubeAffineH1LinearMap d r (c', matVecMul S⁻¹ e')
  have hphysicalMem : MemLp
      (fun x ↦ u.toFun x - (c' + vecDot (matVecMul S⁻¹ e') x)) 2
      (normalizedCubeMeasure (originCube d r)) := by
    have hraw := (uR - ellUR).memL2_normalizedCubeMeasure
    rw [H1Function.sub_toFun] at hraw
    rw [originCubeAffineH1LinearMap_toFun] at hraw
    exact hraw
  have hchildNorm := roundedPullback_child_candidate_cubeLpNorm_le
    abar hS r u.toFun vP.toFun (by simpa only [S, A] using hvPfun)
    c' e' (by simpa only [S, A] using hphysicalMem)
    (by rw [hchildScale]; exact houterMem)
  have hweightChild : cubeBesovScaleWeight 1 (originCube d r) =
      (3 : ℝ) ^ G * cubeBesovScaleWeight 1
        (originCube d (kp - (M : ℤ))) := by
    rw [← hchildScale]
    simpa only [show r + (G : ℤ) - (G : ℤ) = r by omega] using
      cubeBesovScaleWeight_one_originCube_sub_nat_roundDecay
        (d := d) (r + (G : ℤ)) G
  have hchildError :
      normalizedAffineCandidateError (originCube d r) u.toFun c'
          (matVecMul S⁻¹ e') ≤
        P * normalizedAffineCandidateError
          (originCube d (kp - (M : ℤ))) vP.toFun c' e' := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance
    rw [hweightChild]
    calc
      ((3 : ℝ) ^ G * cubeBesovScaleWeight 1
          (originCube d (kp - (M : ℤ)))) *
          cubeLpNorm (originCube d r) 2
            (fun x ↦ u.toFun x - (c' + vecDot (matVecMul S⁻¹ e') x)) ≤
        ((3 : ℝ) ^ G * cubeBesovScaleWeight 1
          (originCube d (kp - (M : ℤ)))) *
          (K * cubeLpNorm (originCube d (kp - (M : ℤ))) 2
            (fun y ↦ vP.toFun y - (c' + vecDot e' y))) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa only [K, G, S, A, hchildScale] using hchildNorm)
            (mul_nonneg (by positivity) (cubeBesovScaleWeight_nonneg 1 _))
      _ = P * (cubeBesovScaleWeight 1
          (originCube d (kp - (M : ℤ))) *
          cubeLpNorm (originCube d (kp - (M : ℤ))) 2
            (fun y ↦ vP.toFun y - (c' + vecDot e' y))) := by
        dsimp [P]
        ring
  refine ⟨c', matVecMul S⁻¹ e', ?_⟩
  rw [show k - (N : ℤ) = r from rfl]
  calc
    normalizedAffineCandidateError (originCube d r) u.toFun c'
          (matVecMul S⁻¹ e') ≤
        P * normalizedAffineCandidateError
          (originCube d (kp - (M : ℤ))) vP.toFun c' e' := hchildError
    _ ≤ P * (C₀ * ((1 : ℝ) / 3) ^ t *
          normalizedAffineCandidateError
            (originCube d kp) vP.toFun c (matVecMul S e)) :=
      mul_le_mul_of_nonneg_left hdecay' hP
    _ ≤ P * (C₀ * ((1 : ℝ) / 3) ^ t *
          (P * normalizedAffineCandidateError
            (originCube d k) u.toFun c e)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hparentError
          (mul_nonneg hC₀.le (by positivity))) hP
    _ = (P * (C₀ * ((1 : ℝ) / 3) ^ t * P)) *
          normalizedAffineCandidateError (originCube d k) u.toFun c e := by ring
    _ ≤ theta * normalizedAffineCandidateError
          (originCube d k) u.toFun c e :=
      mul_le_mul_of_nonneg_right hcoef
        (normalizedAffineCandidateError_nonneg _ _ _ _)

end

end HighContrast
end HCPolySupport
