/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormFoundations
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Entry.Geometry.CanonicalMetricBounds
public import LeanPool.HighContrastHomogenization.Entry.Geometry.GeometryUpdateBounds
public import LeanPool.HighContrastHomogenization.Entry.Geometry.ProjectiveMetric
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridComparison
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.DriftAdvance
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.GeometricMean
public import LeanPool.HighContrastHomogenization.Entry.InitialFixedGridScale
public import LeanPool.HighContrastHomogenization.Entry.OneGridPropagation
public import LeanPool.HighContrastHomogenization.Entry.ScaleSelection
public import LeanPool.HighContrastHomogenization.Entry.Setup.SelectionData
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# High-contrast homogenization: Entry.Multiscale.Global.GeoMeanBlocks

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Block plumbing and the projective-distance sandwich

Block-matrix plumbing for the Loewner order (`matLE_iff`, `le_of_blockMatLoewnerLE`,
`toFullBlockMat_blockScale`,
the `lowerRight` transfer lemmas), the projective-distance sandwich
`projectiveDistance_le_of_sandwich`, and the identification of the canonical metric with a
matrix geometric mean. These are the helpers the public toolkit
`HCPoly.Entry.Multiscale.Initial.GeometricMean` (namespace `GeometricMean`) does not itself carry;
the
square-root order and geometric-mean facts are taken from there. They supply the block-order and
matrix-geometric-mean part of the canonical-metric comparison in the finite run of
`p.global.selection`, bounding the projective distance between two canonical metrics by half the
logarithm of the Loewner sandwich ratio.
-/

open HCPolySupport.HighContrast (blockLogDet blockMatEntry_blockScale blockScale matSqrt
  matSqrt_spec normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale.BlockGeometricMean

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

open Matrix
open scoped MatrixOrder

/-! ## Part 2. Block plumbing -/

section Blocks

variable {d : ℕ}

theorem matLE_iff {A B : Mat d} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ≤ B ↔ MatLoewnerLE A B := by
  constructor
  · intro h x
    have ht := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at ht
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp ht) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · intro h
    refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_)
    intro x
    have hx := h x
    change 1 / 2 * (x ⬝ᵥ A.mulVec x) ≤ 1 / 2 * (x ⬝ᵥ B.mulVec x) at hx
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    linarith only [hx]

theorem symm_blockScale {c : ℝ} {E : BlockMat d} (hE : IsSymmetricBlockMat E) :
    IsSymmetricBlockMat (blockScale c E) := by
  intro a b
  rw [blockMatEntry_blockScale, blockMatEntry_blockScale, hE a b]

theorem lowerRight_ofFull (M : FullBlockMat d) :
    (ofFullBlockMat M).lowerRight = M.submatrix Sum.inr Sum.inr := rfl

theorem lowerRightMono {M N : FullBlockMat d} (h : M ≤ N) :
    (ofFullBlockMat M).lowerRight ≤ (ofFullBlockMat N).lowerRight := by
  have hps := (Matrix.le_iff.mp h).submatrix (Sum.inr : Fin d → BlockCoord d)
  rw [lowerRight_ofFull, lowerRight_ofFull]
  refine Matrix.le_iff.mpr ?_
  simpa [Matrix.submatrix_sub] using hps

theorem lowerRight_smul (a : ℝ) (M : FullBlockMat d) :
    (ofFullBlockMat (a • M)).lowerRight = a • (ofFullBlockMat M).lowerRight := rfl

end Blocks

/-! ## Part 3. The projective-distance sandwich -/

theorem projectiveDistance_le_of_sandwich {d : ℕ} [NeZero d] {m₀ m₁ : Mat d}
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) {a b : ℝ} (ha : 0 < a)
    (hlo : MatLoewnerLE (a • m₀) m₁) (hhi : MatLoewnerLE m₁ (b • m₀)) :
    projectiveDistance m₀ m₁ ≤ 1 / 2 * Real.log (b / a) := by
  obtain ⟨L, U, hL, hLU, hlow, hup, _hLdef, _hUdef, hdist⟩ :=
    Geometry.projectiveDistance_eq_log_relative_spread h₀ h₁
  have haL : a ≤ L := (hlow a).1 hlo
  have hUb : U ≤ b := (hup b).1 hhi
  have hUL : U / L ≤ b / a := by
    have hLinv : (0:ℝ) < L⁻¹ := inv_pos.mpr hL
    have hstep : L⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hL ha).2 haL
    have hUpos : (0:ℝ) < U := lt_of_lt_of_le hL hLU
    have h1 : U * L⁻¹ ≤ b * a⁻¹ :=
      calc U * L⁻¹ ≤ b * L⁻¹ := mul_le_mul_of_nonneg_right hUb hLinv.le
        _ ≤ b * a⁻¹ :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt (lt_of_lt_of_le hUpos hUb))
    simpa [div_eq_mul_inv] using h1
  rw [hdist]
  have hpos : 0 < U / L := div_pos (lt_of_lt_of_le hL hLU) hL
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hUL) (by norm_num)

/-! ## Part 4. The canonical metric as a geometric mean -/

theorem explicitCanonicalMetric_eq_geoMean {d : ℕ} (F : BlockMat d) :
    explicitCanonicalMetric F =
      ((ofFullBlockMat (GeometricMean.geoMean (toFullBlockMat F)
        (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ *
          toFullBlockMat (blockSwap d)))).lowerRight)⁻¹ := by
  have h : matSqrt ((toFullBlockMat F)⁻¹) *
        (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d)) *
        matSqrt ((toFullBlockMat F)⁻¹)
      = matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ *
          toFullBlockMat (blockSwap d) * matSqrt ((toFullBlockMat F)⁻¹) := by
    noncomm_ring
  unfold explicitCanonicalMetric GeometricMean.geoMean
  rw [h]

theorem lowerRightPosDef {d : ℕ} {M : FullBlockMat d} (hM : M.PosDef) :
    (ofFullBlockMat M).lowerRight.PosDef := by
  rw [lowerRight_ofFull]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hM.isHermitian.submatrix Sum.inr) ?_
  intro x hx
  have hne : Sum.elim (0 : Fin d → ℝ) x ≠ 0 := by
    intro he
    apply hx
    funext i
    have hi := congrFun he (Sum.inr i)
    simpa using hi
  have h := hM.dotProduct_mulVec_pos hne
  simpa only [star_trivial, Matrix.mulVec, Matrix.submatrix_apply, dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero] using h

theorem swapFullHerm (d : ℕ) :
    (toFullBlockMat (blockSwap d))ᴴ = toFullBlockMat (blockSwap d) := by
  ext α β
  cases α <;> cases β <;>
    simp [blockSwap, Book.Ch02.blockR, toFullBlockMat, Matrix.conjTranspose,
      Matrix.one_apply, eq_comm]

theorem sandwich {d : ℕ} [NeZero d]
    (F G : BlockMat d)
    (hF : IsSymmetricBlockMat F) (hFpos : Book.Ch02.BlockPosDef F)
    (hG : IsSymmetricBlockMat G) (hGpos : Book.Ch02.BlockPosDef G)
    (c κ : ℝ) (hc : 0 < c) (hκ : 1 ≤ κ)
    (hlo : BlockMatLoewnerLE (blockScale c G) F)
    (hhi : BlockMatLoewnerLE F (blockScale (κ * c) G)) :
    projectiveDistance (explicitCanonicalMetric F) (explicitCanonicalMetric G) ≤ 1 / 2 * Real.log κ := by
  have hκ0 : (0:ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκc : (0:ℝ) < κ * c := mul_pos hκ0 hc
  have hRsymm := swapFullHerm d
  have hAFpos : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hF hFpos
  have hAGpos : (toFullBlockMat G).PosDef := posDef_toFullBlockMat hG hGpos
  have hSF : (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ *
      toFullBlockMat (blockSwap d)).PosDef := Geometry.swapConj_inv_posDef hF hFpos
  have hSG : (toFullBlockMat (blockSwap d) * (toFullBlockMat G)⁻¹ *
      toFullBlockMat (blockSwap d)).PosDef := Geometry.swapConj_inv_posDef hG hGpos
  rw [explicitCanonicalMetric_eq_geoMean F, explicitCanonicalMetric_eq_geoMean G]
  set RR : FullBlockMat d := toFullBlockMat (blockSwap d)
  set AF : FullBlockMat d := toFullBlockMat F
  set AG : FullBlockMat d := toFullBlockMat G
  -- the two block comparisons, transported to the full matrices
  have hloF : c • AG ≤ AF := by
    have h := le_of_blockMatLoewnerLE (symm_blockScale hG) hF hlo
    rwa [toFullBlockMat_blockScale] at h
  have hhiF : AF ≤ (κ * c) • AG := by
    have h := le_of_blockMatLoewnerLE hF (symm_blockScale hG) hhi
    rwa [toFullBlockMat_blockScale] at h
  have hcG : (c • AG).PosDef := hAGpos.smul hc
  have hkcG : ((κ * c) • AG).PosDef := hAGpos.smul hκc
  -- inverses reverse the order, and conjugation by `R` preserves it
  have hinv1 : AF⁻¹ ≤ c⁻¹ • AG⁻¹ := by
    have h := HCPolySupport.HighContrast.inv_le_inv_of_le hcG hAFpos hloF
    rwa [GeometricMean.inv_smul_of_posDef hAGpos hc.ne'] at h
  have hinv2 : (κ * c)⁻¹ • AG⁻¹ ≤ AF⁻¹ := by
    have h := HCPolySupport.HighContrast.inv_le_inv_of_le hAFpos hkcG hhiF
    rwa [GeometricMean.inv_smul_of_posDef hAGpos hκc.ne'] at h
  have hconj1 : RR * AF⁻¹ * RR ≤ c⁻¹ • (RR * AG⁻¹ * RR) := by
    have h := HCPolySupport.HighContrast.conj_le_conj' hRsymm hinv1
    rwa [show RR * (c⁻¹ • AG⁻¹) * RR = c⁻¹ • (RR * AG⁻¹ * RR) by
      simp] at h
  have hconj2 : (κ * c)⁻¹ • (RR * AG⁻¹ * RR) ≤ RR * AF⁻¹ * RR := by
    have h := HCPolySupport.HighContrast.conj_le_conj' hRsymm hinv2
    rwa [show RR * ((κ * c)⁻¹ • AG⁻¹) * RR = (κ * c)⁻¹ • (RR * AG⁻¹ * RR) by
      simp] at h
  -- joint monotonicity and homogeneity of the geometric mean
  have harg1 : c * (κ * c)⁻¹ = κ⁻¹ := by field_simp
  have harg2 : (κ * c) * c⁻¹ = κ := by field_simp
  have hMlo : (Real.sqrt κ)⁻¹ • GeometricMean.geoMean AG (RR * AG⁻¹ * RR) ≤ GeometricMean.geoMean AF (RR * AF⁻¹ * RR) := by
    have h := GeometricMean.geoMean_mono hcG hAFpos (hSG.smul (inv_pos.mpr hκc)) hSF hloF hconj2
    rwa [GeometricMean.geoMean_smul hAGpos hSG hc (inv_pos.mpr hκc), harg1, Real.sqrt_inv] at h
  have hMhi : GeometricMean.geoMean AF (RR * AF⁻¹ * RR) ≤ Real.sqrt κ • GeometricMean.geoMean AG (RR * AG⁻¹ * RR) := by
    have h := GeometricMean.geoMean_mono hAFpos hkcG hSF (hSG.smul (inv_pos.mpr hc)) hhiF hconj1
    rwa [GeometricMean.geoMean_smul hAGpos hSG hκc (inv_pos.mpr hc), harg2] at h
  -- pass to the lower-right blocks and invert
  have hsk : (0:ℝ) < Real.sqrt κ := Real.sqrt_pos.mpr hκ0
  have hMFpos : (GeometricMean.geoMean AF (RR * AF⁻¹ * RR)).PosDef := GeometricMean.geoMeanPosDef hAFpos hSF
  have hMGpos : (GeometricMean.geoMean AG (RR * AG⁻¹ * RR)).PosDef := GeometricMean.geoMeanPosDef hAGpos hSG
  have hLF : (ofFullBlockMat (GeometricMean.geoMean AF (RR * AF⁻¹ * RR))).lowerRight.PosDef :=
    lowerRightPosDef hMFpos
  have hLG : (ofFullBlockMat (GeometricMean.geoMean AG (RR * AG⁻¹ * RR))).lowerRight.PosDef :=
    lowerRightPosDef hMGpos
  have hLlo : (Real.sqrt κ)⁻¹ • (ofFullBlockMat (GeometricMean.geoMean AG (RR * AG⁻¹ * RR))).lowerRight ≤
      (ofFullBlockMat (GeometricMean.geoMean AF (RR * AF⁻¹ * RR))).lowerRight := by
    have h := lowerRightMono hMlo
    rwa [lowerRight_smul] at h
  have hLhi : (ofFullBlockMat (GeometricMean.geoMean AF (RR * AF⁻¹ * RR))).lowerRight ≤
      Real.sqrt κ • (ofFullBlockMat (GeometricMean.geoMean AG (RR * AG⁻¹ * RR))).lowerRight := by
    have h := lowerRightMono hMhi
    rwa [lowerRight_smul] at h
  set LF := (ofFullBlockMat (GeometricMean.geoMean AF (RR * AF⁻¹ * RR))).lowerRight
  set LG := (ofFullBlockMat (GeometricMean.geoMean AG (RR * AG⁻¹ * RR))).lowerRight
  have hmF : (LF⁻¹).PosDef := hLF.inv
  have hmG : (LG⁻¹).PosDef := hLG.inv
  have hstep1 : LF⁻¹ ≤ Real.sqrt κ • LG⁻¹ := by
    have h := HCPolySupport.HighContrast.inv_le_inv_of_le (hLG.smul (inv_pos.mpr hsk)) hLF hLlo
    rwa [GeometricMean.inv_smul_of_posDef hLG (inv_pos.mpr hsk).ne', inv_inv] at h
  have hstep2 : (Real.sqrt κ)⁻¹ • LG⁻¹ ≤ LF⁻¹ := by
    have h := HCPolySupport.HighContrast.inv_le_inv_of_le hLF (hLG.smul hsk) hLhi
    rwa [GeometricMean.inv_smul_of_posDef hLG hsk.ne'] at h
  have hstep3 : (Real.sqrt κ)⁻¹ • LF⁻¹ ≤ LG⁻¹ := by
    have h := smul_le_smul_of_nonneg_left hstep1 (le_of_lt (inv_pos.mpr hsk))
    rwa [smul_smul, inv_mul_cancel₀ hsk.ne', one_smul] at h
  have hstep4 : LG⁻¹ ≤ Real.sqrt κ • LF⁻¹ := by
    have h := smul_le_smul_of_nonneg_left hstep2 (le_of_lt hsk)
    rwa [smul_smul, mul_inv_cancel₀ hsk.ne', one_smul] at h
  -- the projective sandwich
  have hlo' : MatLoewnerLE ((Real.sqrt κ)⁻¹ • LF⁻¹) (LG⁻¹) :=
    (matLE_iff (hmF.smul (inv_pos.mpr hsk)).isHermitian hmG.isHermitian).1 hstep3
  have hhi' : MatLoewnerLE (LG⁻¹) (Real.sqrt κ • LF⁻¹) :=
    (matLE_iff hmG.isHermitian (hmF.smul hsk).isHermitian).1 hstep4
  have hfin := projectiveDistance_le_of_sandwich hmF hmG (inv_pos.mpr hsk) hlo' hhi'
  have hratio : Real.sqrt κ / (Real.sqrt κ)⁻¹ = κ := by
    field_simp
    exact Real.sq_sqrt hκ0.le
  rwa [hratio] at hfin

/-- Block-plumbing step for `explicitCanonicalMetric_projectiveDistance_le_logDet`: unit scaling
of a
symmetric positive block preserves a Loewner bound above another such block. -/
theorem explicitCanonicalMetric_projectiveDistance_le_logDet_aux_scale_one_le {d : ℕ} (G F : BlockMat d) (hGs : IsSymmetricBlockMat G)
    (hG : Book.Ch02.BlockPosDef G) (hFs : IsSymmetricBlockMat F)
    (hF : Book.Ch02.BlockPosDef F) (hGF : BlockMatLoewnerLE G F) :
    BlockMatLoewnerLE (blockScale (1 : ℝ) G) F := by
  have hAF : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hFs hF
  have hAG : (toFullBlockMat G).PosDef := posDef_toFullBlockMat hGs hG
  have hherm : (toFullBlockMat (blockScale (1 : ℝ) G)).IsHermitian := by
    rw [toFullBlockMat_blockScale, one_smul]
    exact hAG.isHermitian
  refine (Annealed.fullBlock_le_iff hherm hAF.isHermitian).1 ?_
  rw [toFullBlockMat_blockScale, one_smul]
  exact (Annealed.fullBlock_le_iff hAG.isHermitian hAF.isHermitian).2 hGF

/-- Projective-distance-sandwich step for `explicitCanonicalMetric_projectiveDistance_le_logDet`:
for
symmetric positive blocks `G ≤ F`, `F` is Loewner-below `exp(logDet F − logDet G) • G`, and the
exponent is nonnegative. -/
theorem explicitCanonicalMetric_projectiveDistance_le_logDet_aux_upper {d : ℕ} (F G : BlockMat d) (hFs : IsSymmetricBlockMat F)
    (hF : Book.Ch02.BlockPosDef F) (hGs : IsSymmetricBlockMat G)
    (hG : Book.Ch02.BlockPosDef G) (hGF : BlockMatLoewnerLE G F) :
    BlockMatLoewnerLE F (blockScale (Real.exp (blockLogDet F - blockLogDet G)) G) ∧
      0 ≤ blockLogDet F - blockLogDet G := by
  have hAF : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hFs hF
  have hAG : (toFullBlockMat G).PosDef := posDef_toFullBlockMat hGs hG
  obtain ⟨-, hloss, -, hnorm, -, -⟩ :=
    Annealed.normalizedBlock_order_consequences 0 F G hAF hAG hGF
  refine ⟨?_, hloss⟩
  have hκpos : (0 : ℝ) < Real.exp (blockLogDet F - blockLogDet G) := Real.exp_pos _
  have hS : (matSqrt ((toFullBlockMat G)⁻¹)).PosDef := matSqrt_inv_posDef_full hAG
  have hC : (matSqrt ((toFullBlockMat G)⁻¹) * toFullBlockMat F *
      matSqrt ((toFullBlockMat G)⁻¹)).PosSemidef := by
    have h := hAF.posSemidef.conjTranspose_mul_mul_same (matSqrt ((toFullBlockMat G)⁻¹))
    rwa [hS.isHermitian.eq] at h
  have hnorm' : ‖matSqrt ((toFullBlockMat G)⁻¹) * toFullBlockMat F *
      matSqrt ((toFullBlockMat G)⁻¹)‖ ≤ Real.exp (blockLogDet F - blockLogDet G) := by
    have h := hnorm
    simp only [blockOpNorm, normalizedBlock, toFullBlockMat_ofFullBlockMat] at h
    exact h
  have hCle := GeometricMean.le_smul_one_of_norm_le hC hnorm'
  have hTherm : (matSqrt (toFullBlockMat G))ᴴ = matSqrt (toFullBlockMat G) :=
    HCPolySupport.HighContrast.conjTranspose_matSqrt hAG.posSemidef
  obtain ⟨hTS, hST⟩ := GeometricMean.sqrtCancel hAG
  have hTT : matSqrt (toFullBlockMat G) * matSqrt (toFullBlockMat G) = toFullBlockMat G :=
    (matSqrt_spec hAG.posSemidef).2
  have hconj := HCPolySupport.HighContrast.conj_le_conj' hTherm hCle
  have hL : matSqrt (toFullBlockMat G) *
      (matSqrt ((toFullBlockMat G)⁻¹) * toFullBlockMat F *
        matSqrt ((toFullBlockMat G)⁻¹)) * matSqrt (toFullBlockMat G) = toFullBlockMat F := by
    calc matSqrt (toFullBlockMat G) *
          (matSqrt ((toFullBlockMat G)⁻¹) * toFullBlockMat F *
            matSqrt ((toFullBlockMat G)⁻¹)) * matSqrt (toFullBlockMat G)
        = (matSqrt (toFullBlockMat G) * matSqrt ((toFullBlockMat G)⁻¹)) * toFullBlockMat F *
            (matSqrt ((toFullBlockMat G)⁻¹) * matSqrt (toFullBlockMat G)) := by noncomm_ring
      _ = toFullBlockMat F := by
          rw [hTS, hST, Matrix.one_mul, Matrix.mul_one]
  have hR : matSqrt (toFullBlockMat G) *
      (Real.exp (blockLogDet F - blockLogDet G) • (1 : FullBlockMat d)) *
        matSqrt (toFullBlockMat G)
      = Real.exp (blockLogDet F - blockLogDet G) • toFullBlockMat G := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hTT]
  rw [hL, hR] at hconj
  have hherm : (toFullBlockMat (blockScale
      (Real.exp (blockLogDet F - blockLogDet G)) G)).IsHermitian := by
    rw [toFullBlockMat_blockScale]
    exact (hAG.smul hκpos).isHermitian
  refine (Annealed.fullBlock_le_iff hAF.isHermitian hherm).1 ?_
  rw [toFullBlockMat_blockScale]
  exact hconj



end

end HCPolySupport.HighContrast.Multiscale.BlockGeometricMean
