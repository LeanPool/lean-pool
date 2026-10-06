/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSharpConstant
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSupplyPorts

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastDesignConstantBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The design instantiation's two constant bounds

The recursion constant of the endpoint is read at the isotropy carriers, and
two of its arguments still name the reference block: the drop constant, whose
value is the relative size of the block inside its own scalar multiple, and —
through it — the recursion constant itself.  Both are bounded by
dimension-only numbers.

* the relative size of a block inside `c` times itself is at most `c⁻¹`, so the
  drop constant at the isotropy reference is at most `4`;
* the recursion constant is monotone in the drop slot, so replacing the drop
  constant by `4` only enlarges it.

Together these are what lets the endpoint fix its decay rate before the
reference block exists.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## 1. The relative size inside a scalar multiple -/

/-- **A block inside a positive multiple of itself.**  The relative size is at
most the reciprocal of the multiple. -/
theorem blockSize_blockScale_self_le [NeZero d] {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) {c : ℝ} (hc : 0 < c) :
    blockSize E (blockScale c E) ≤ c⁻¹ := by
  have hscaleSym : IsSymmetricBlockMat (blockScale c E) :=
    isSymmetricBlockMat_blockScale c hE
  have hscalePd : BlockPosDef (blockScale c E) := by
    intro X hX
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
    exact mul_pos hc (hEpd X hX)
  have hPS : (toFullBlockMat E).PosSemidef :=
    (posDef_toFullBlockMat hE hEpd).posSemidef
  have hnn : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul E X) := by
    intro X
    have hx := hPS.dotProduct_mulVec_nonneg (toFullBlockVec X)
    simp only [star_trivial] at hx
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    linarith only [hx]
  have hidem : (c⁻¹ : ℝ) • toFullBlockMat (blockScale c E) =
      toFullBlockMat E := by
    rw [toFullBlockMat_blockScale, smul_smul, inv_mul_cancel₀ (ne_of_gt hc),
      one_smul]
  have hnegle : BlockMatLoewnerLE (blockScale (-(c⁻¹)) (blockScale c E)) E := by
    intro X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale,
      Sharp.blockVecDot_blockMatVecMul_blockScale]
    have h := hnn X
    have hid : -(c⁻¹) * (c * blockVecDot X (blockMatVecMul E X)) =
        -blockVecDot X (blockMatVecMul E X) := by
      field_simp
    rw [hid]
    linarith only [h]
  refine PortableHistory.blockSize_le_of_sandwich hE hscaleSym hscalePd
    (le_of_lt (inv_pos.mpr hc)) (le_of_eq hidem.symm) ?_
  have h := le_of_blockMatLoewnerLE
    (isSymmetricBlockMat_blockScale (-(c⁻¹)) hscaleSym) hE hnegle
  rwa [toFullBlockMat_blockScale (-(c⁻¹))] at h

/-- **The drop constant at the isotropy reference is at most four.** -/
theorem dropConstantIsotropy_isotropyReference_le [NeZero d] {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) {cIso : ℝ}
    (hcIso : 0 ≤ cIso) :
    dropConstantIsotropy (1 + cIso) E (isotropyReference cIso E) ≤ 4 := by
  have hc : (0 : ℝ) < 1 + cIso := by linarith only [hcIso]
  have hsize : blockSize E (isotropyReference cIso E) ≤ (1 + cIso)⁻¹ := by
    rw [isotropyReference_eq_blockScale]
    exact blockSize_blockScale_self_le hE hEpd hc
  have hstep : 4 * (1 + cIso) * blockSize E (isotropyReference cIso E) ≤
      4 * (1 + cIso) * (1 + cIso)⁻¹ :=
    mul_le_mul_of_nonneg_left hsize (by linarith only [hcIso])
  have hid : (1 + cIso) * (1 + cIso)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hc)
  rw [dropConstantIsotropy]
  have hrw : 4 * (1 + cIso) * (1 + cIso)⁻¹ = 4 * ((1 + cIso) * (1 + cIso)⁻¹) := by
    ring
  rw [hrw, hid] at hstep
  linarith only [hstep]

/-! ## 2. Monotonicity of the recursion constant in the drop slot -/

/-- The drop-group constant is monotone in the drop constant. -/
theorem weakDropConstant_mono_cD {M L alpha cD cD' delta : ℝ}
    (halpha : 0 < alpha) (hdelta : 0 ≤ delta) (hcD : cD ≤ cD') :
    weakDropConstant (d := d) M L alpha cD delta ≤
      weakDropConstant (d := d) M L alpha cD' delta := by
  have hlt : (3 : ℝ) ^ (-alpha) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [halpha])
  have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-alpha) := by linarith only [hlt]
  have hinv0 : (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-alpha))⁻¹ :=
    le_of_lt (inv_pos.mpr hpos)
  have hhalf0 : (0 : ℝ) ≤ halfGeom := le_of_lt halfGeom_pos
  have hcoef0 : (0 : ℝ) ≤ 2 * (16 * M * Real.sqrt L) ^ 2 := by positivity
  have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  have h1 : delta * halfGeom * (cD * halfGeom) ≤
      delta * halfGeom * (cD' * halfGeom) := by
    have hfac : (0 : ℝ) ≤ delta * halfGeom := mul_nonneg hdelta hhalf0
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcD hhalf0) hfac
  have h2 : (1 - (3 : ℝ) ^ (-alpha))⁻¹ *
        (2 * (d : ℝ) * (cD * (1 - (3 : ℝ) ^ (-alpha))⁻¹)) ≤
      (1 - (3 : ℝ) ^ (-alpha))⁻¹ *
        (2 * (d : ℝ) * (cD' * (1 - (3 : ℝ) ^ (-alpha))⁻¹)) := by
    refine mul_le_mul_of_nonneg_left ?_ hinv0
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcD hinv0) hd0
  rw [weakDropConstant, weakDropConstant]
  have hsum : delta * halfGeom * (cD * halfGeom) +
      (1 - (3 : ℝ) ^ (-alpha))⁻¹ *
        (2 * (d : ℝ) * (cD * (1 - (3 : ℝ) ^ (-alpha))⁻¹)) ≤
      delta * halfGeom * (cD' * halfGeom) +
      (1 - (3 : ℝ) ^ (-alpha))⁻¹ *
        (2 * (d : ℝ) * (cD' * (1 - (3 : ℝ) ^ (-alpha))⁻¹)) := by
    linarith only [h1, h2]
  exact mul_le_mul_of_nonneg_left hsum hcoef0

/-- **The recursion constant is monotone in the drop slot.** -/
theorem fusionRecursionConstantIsotropySharp_mono_cD (d : ℕ) {Cpre eta : ℝ} (H : ℕ)
    {M L g cRow kap cD cD' delta cVsum cVm : ℝ}
    (hCpre : 0 ≤ Cpre) (hg1 : g < 1) (hdelta : 0 ≤ delta) (hcD : cD ≤ cD') :
    fusionRecursionConstantIsotropySharp d Cpre eta H M L g cRow kap cD delta
        cVsum cVm ≤
      fusionRecursionConstantIsotropySharp d Cpre eta H M L g cRow kap cD' delta
        cVsum cVm := by
  have hw0 : (0 : ℝ) ≤ 3 * weakCoefficient d Cpre := by
    have := weakCoefficient_nonneg d hCpre
    linarith only [this]
  have hdropmono := weakDropConstant_mono_cD (d := d) (M := M) (L := L)
    (contrastAlpha_pos hg1) hdelta hcD
  have hbranch : dropCoefficient d Cpre eta *
        ((((3 : ℝ) ^ (-recursionAlpha g)) ^ H)⁻¹) +
      3 * weakCoefficient d Cpre *
        weakDropConstant (d := d) M L (contrastAlpha g) cD delta ≤
      dropCoefficient d Cpre eta *
        ((((3 : ℝ) ^ (-recursionAlpha g)) ^ H)⁻¹) +
      3 * weakCoefficient d Cpre *
        weakDropConstant (d := d) M L (contrastAlpha g) cD' delta := by
    have := mul_le_mul_of_nonneg_left hdropmono hw0
    linarith only [this]
  rw [fusionRecursionConstantIsotropySharp, fusionRecursionConstantIsotropySharp]
  refine max_le_max le_rfl (max_le_max hbranch le_rfl)

end

end HCPolySupport.HighContrast.Quenched
