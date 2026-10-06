/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.GeometricMean

/-!
# High-contrast homogenization: Entry.Multiscale.Initial.CanonicalMetric

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Initialization: the canonical metric, the projective sandwich and the entry radius

The two deterministic kernels A17 and A18 of the initialization route and the entry-radius
estimate they prove (`p.initial.fixed.grid.scale`, the printed
"entry-radius estimate"; the geometric-mean monotonicity is
`p.global.selection`).  Block plumbing, the
projective-distance sandwich, and the identification of the canonical metric of a block
matrix with a matrix geometric mean are proved first.

Hermitian symmetry of `skewCorrectedForm E h` is proved here from block symmetry and the
public `posDef_lowerRight`; `HCPoly/Entry/Analysis/ReferenceComparison.lean` has no public original
for it (its `corrected_pos` proves the stronger `PosDef` privately).  The two facts that
file does export, `swapConj_lowerRight` and `schurSigma_le_corrected`, are used directly.

No probability law and no annealed premise enters any statement of this file.
-/

open HCPolySupport.HighContrast (aspectRatio bigLambdaRef blockMatEntry_blockScale blockScale
  exists_isSkewMat_bigLambdaRef_eq lambdaRef matLoewnerLE_specBound_smul_one matSqrt
  posDef_lowerRight schurSigma schurSkew skewCorrectedForm specBound)
namespace HCPolySupport.HighContrast.Multiscale

open Matrix
open GeometricMean
open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-! ## Part 2. Block plumbing -/

section Blocks

variable {d : ℕ}

private theorem matLE_iff {A B : Mat d} (hA : A.IsHermitian) (hB : B.IsHermitian) :
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

private theorem fullLE_of_block {A B : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hB : IsSymmetricBlockMat B) (h : BlockMatLoewnerLE A B) :
    toFullBlockMat A ≤ toFullBlockMat B := by
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (((Analysis.toFullBlockMat_isHermitian_iff B).2 hB).sub
      ((Analysis.toFullBlockMat_isHermitian_iff A).2 hA)) ?_)
  intro x
  have hx := h (ofFullBlockVec x)
  simp only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
    toFullBlockVec_ofFullBlockVec] at hx
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
  linarith only [hx]

private theorem symm_blockScale {c : ℝ} {E : BlockMat d} (hE : IsSymmetricBlockMat E) :
    IsSymmetricBlockMat (blockScale c E) := by
  intro a b
  rw [blockMatEntry_blockScale, blockMatEntry_blockScale, hE a b]

private theorem lowerRight_ofFull (M : FullBlockMat d) :
    (ofFullBlockMat M).lowerRight = M.submatrix Sum.inr Sum.inr := rfl

private theorem lowerRightMono {M N : FullBlockMat d} (h : M ≤ N) :
    (ofFullBlockMat M).lowerRight ≤ (ofFullBlockMat N).lowerRight := by
  have hps := (Matrix.le_iff.mp h).submatrix (Sum.inr : Fin d → BlockCoord d)
  rw [lowerRight_ofFull, lowerRight_ofFull]
  refine Matrix.le_iff.mpr ?_
  simpa [Matrix.submatrix_sub] using hps

private theorem lowerRight_smul (a : ℝ) (M : FullBlockMat d) :
    (ofFullBlockMat (a • M)).lowerRight = a • (ofFullBlockMat M).lowerRight := rfl

end Blocks

/-! ## Part 3. The projective-distance sandwich -/

private theorem projectiveDistance_le_of_sandwich {d : ℕ} [NeZero d] {m₀ m₁ : Mat d}
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
    have hb : 0 ≤ b := le_trans (le_of_lt hUpos) hUb
    have h1 : U * L⁻¹ ≤ b * a⁻¹ := by
      calc
        U * L⁻¹ ≤ b * L⁻¹ := mul_le_mul_of_nonneg_right hUb (le_of_lt hLinv)
        _ ≤ b * a⁻¹ := mul_le_mul_of_nonneg_left hstep hb
    simpa [div_eq_mul_inv] using h1
  rw [hdist]
  have hpos : 0 < U / L := div_pos (lt_of_lt_of_le hL hLU) hL
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hUL) (by norm_num)

/-! ## Part 4. The canonical metric as a geometric mean -/

private theorem explicitCanonicalMetric_eq_geoMean {d : ℕ} (F : BlockMat d) :
    explicitCanonicalMetric F =
      ((ofFullBlockMat (geoMean (toFullBlockMat F)
        (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ *
          toFullBlockMat (blockSwap d)))).lowerRight)⁻¹ := by
  have h : matSqrt ((toFullBlockMat F)⁻¹) *
        (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d)) *
        matSqrt ((toFullBlockMat F)⁻¹)
      = matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ *
          toFullBlockMat (blockSwap d) * matSqrt ((toFullBlockMat F)⁻¹) := by
    noncomm_ring
  unfold explicitCanonicalMetric geoMean
  rw [h]

private theorem lowerRightPosDef {d : ℕ} {M : FullBlockMat d} (hM : M.PosDef) :
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

private theorem swapFullHerm (d : ℕ) :
    (toFullBlockMat (blockSwap d))ᴴ = toFullBlockMat (blockSwap d) := by
  ext α β
  cases α <;> cases β <;>
    simp [blockSwap, Book.Ch02.blockR, toFullBlockMat, Matrix.conjTranspose,
      Matrix.one_apply, eq_comm]

/-! ### Hermitian symmetry of the skew-corrected form

`HCPoly/Entry/Analysis/ReferenceComparison.lean` exports `swapConj_lowerRight` and
`schurSigma_le_corrected`; both are used below through those public originals.  The one
extra fact needed here, Hermitian symmetry of `skewCorrectedForm E h`, has no public
original there (the private `corrected_pos` of that file proves the stronger `PosDef`), so
it is proved below directly from block symmetry and the public `posDef_lowerRight`, as a
private helper of this file. -/

private theorem upperLeft_isHermitian {d : ℕ} {E : BlockMat d} (hs : IsSymmetricBlockMat E) :
    E.upperLeft.IsHermitian := by
  ext i j
  exact hs (Sum.inl j) (Sum.inl i)

/-- `skewCorrectedForm E h = σ + (k - h)ᵗ σ_* (k - h)` is Hermitian: the correction is a
congruence of the Hermitian block `E.lowerRight`, and `σ = E.upperLeft - kᵗ σ_* k` is a
difference of two such. -/
private theorem skewCorrectedForm_isHermitian {d : ℕ} {E : BlockMat d}
    (hs : IsSymmetricBlockMat E) (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    (skewCorrectedForm E h).IsHermitian := by
  have hD := (posDef_lowerRight hs hp).posSemidef
  have h1 : (matTranspose (schurSkew E) * E.lowerRight * schurSkew E).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (hD.conjTranspose_mul_mul_same (schurSkew E)).isHermitian
  have h2 :
      (matTranspose (schurSkew E - h) * E.lowerRight * (schurSkew E - h)).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (hD.conjTranspose_mul_mul_same (schurSkew E - h)).isHermitian
  simpa only [skewCorrectedForm, schurSigma] using
    (((upperLeft_isHermitian hs).sub h1).add h2)

private theorem hermSmulOne {d : ℕ} (t : ℝ) : ((t • (1 : Mat d)).IsHermitian) := by
  change (t • (1 : Mat d))ᴴ = t • (1 : Mat d)
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_one]

/-- `σ ≤ Λ₀ • 1`.  The derivation of `ReferenceComparison.lean` (inside the public
`refBlock_le_six_aspectRatio_smul_swapConj`), run on `schurSigma_le_corrected`. -/
private theorem schurSigma_le_bigLambdaRef {d : ℕ} [NeZero d] {E : BlockMat d}
    (hs : IsSymmetricBlockMat E) (hp : Book.Ch02.BlockPosDef E) :
    schurSigma E ≤ bigLambdaRef E • (1 : Mat d) := by
  obtain ⟨h, _hh, hLam⟩ := exists_isSkewMat_bigLambdaRef_eq hp
  have hA : skewCorrectedForm E h ≤ bigLambdaRef E • (1 : Mat d) := by
    refine (matLE_iff (skewCorrectedForm_isHermitian hs hp h) (hermSmulOne _)).2 ?_
    rw [hLam]
    exact matLoewnerLE_specBound_smul_one _
  exact (Analysis.schurSigma_le_corrected hs hp h).trans hA


/-- A17 (kernel). Geometric-mean monotonicity and homogeneity
(`p.global.selection`): `cG ≤ F ≤ κcG` gives
`d_pr([m(F)],[m(G)]) ≤ ½ log κ`. -/
theorem explicitCanonicalMetric_projectiveDistance_le_of_sandwich (d : ℕ) (hd : 2 ≤ d)
    (F G : BlockMat d)
    (hF : IsSymmetricBlockMat F) (hFpos : Book.Ch02.BlockPosDef F)
    (hG : IsSymmetricBlockMat G) (hGpos : Book.Ch02.BlockPosDef G)
    (c κ : ℝ) (hc : 0 < c) (hκ : 1 ≤ κ)
    (hlo : BlockMatLoewnerLE (blockScale c G) F)
    (hhi : BlockMatLoewnerLE F (blockScale (κ * c) G)) :
    projectiveDistance (explicitCanonicalMetric F) (explicitCanonicalMetric G) ≤ 1 / 2 * Real.log κ := by
  have : NeZero d := ⟨by omega⟩
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
    have h := fullLE_of_block (symm_blockScale hG) hF hlo
    rwa [toFullBlockMat_blockScale] at h
  have hhiF : AF ≤ (κ * c) • AG := by
    have h := fullLE_of_block hF (symm_blockScale hG) hhi
    rwa [toFullBlockMat_blockScale] at h
  have hcG : (c • AG).PosDef := hAGpos.smul hc
  have hkcG : ((κ * c) • AG).PosDef := hAGpos.smul hκc
  -- inverses reverse the order, and conjugation by `R` preserves it
  have hinv1 : AF⁻¹ ≤ c⁻¹ • AG⁻¹ := by
    have h := inv_le_inv_of_le hcG hAFpos hloF
    rwa [inv_smul_of_posDef hAGpos hc.ne'] at h
  have hinv2 : (κ * c)⁻¹ • AG⁻¹ ≤ AF⁻¹ := by
    have h := inv_le_inv_of_le hAFpos hkcG hhiF
    rwa [inv_smul_of_posDef hAGpos hκc.ne'] at h
  have hconj1 : RR * AF⁻¹ * RR ≤ c⁻¹ • (RR * AG⁻¹ * RR) := by
    have h := conj_le_conj' hRsymm hinv1
    rwa [show RR * (c⁻¹ • AG⁻¹) * RR = c⁻¹ • (RR * AG⁻¹ * RR) by
      simp] at h
  have hconj2 : (κ * c)⁻¹ • (RR * AG⁻¹ * RR) ≤ RR * AF⁻¹ * RR := by
    have h := conj_le_conj' hRsymm hinv2
    rwa [show RR * ((κ * c)⁻¹ • AG⁻¹) * RR = (κ * c)⁻¹ • (RR * AG⁻¹ * RR) by
      simp] at h
  -- joint monotonicity and homogeneity of the geometric mean
  have harg1 : c * (κ * c)⁻¹ = κ⁻¹ := by field_simp
  have harg2 : (κ * c) * c⁻¹ = κ := by field_simp
  have hMlo : (Real.sqrt κ)⁻¹ • geoMean AG (RR * AG⁻¹ * RR) ≤ geoMean AF (RR * AF⁻¹ * RR) := by
    have h := geoMean_mono hcG hAFpos (hSG.smul (inv_pos.mpr hκc)) hSF hloF hconj2
    rwa [geoMean_smul hAGpos hSG hc (inv_pos.mpr hκc), harg1, Real.sqrt_inv] at h
  have hMhi : geoMean AF (RR * AF⁻¹ * RR) ≤ Real.sqrt κ • geoMean AG (RR * AG⁻¹ * RR) := by
    have h := geoMean_mono hAFpos hkcG hSF (hSG.smul (inv_pos.mpr hc)) hhiF hconj1
    rwa [geoMean_smul hAGpos hSG hκc (inv_pos.mpr hc), harg2] at h
  -- pass to the lower-right blocks and invert
  have hsk : (0:ℝ) < Real.sqrt κ := Real.sqrt_pos.mpr hκ0
  have hMFpos : (geoMean AF (RR * AF⁻¹ * RR)).PosDef := geoMeanPosDef hAFpos hSF
  have hMGpos : (geoMean AG (RR * AG⁻¹ * RR)).PosDef := geoMeanPosDef hAGpos hSG
  have hLF : (ofFullBlockMat (geoMean AF (RR * AF⁻¹ * RR))).lowerRight.PosDef :=
    lowerRightPosDef hMFpos
  have hLG : (ofFullBlockMat (geoMean AG (RR * AG⁻¹ * RR))).lowerRight.PosDef :=
    lowerRightPosDef hMGpos
  have hLlo : (Real.sqrt κ)⁻¹ • (ofFullBlockMat (geoMean AG (RR * AG⁻¹ * RR))).lowerRight ≤
      (ofFullBlockMat (geoMean AF (RR * AF⁻¹ * RR))).lowerRight := by
    have h := lowerRightMono hMlo
    rwa [lowerRight_smul] at h
  have hLhi : (ofFullBlockMat (geoMean AF (RR * AF⁻¹ * RR))).lowerRight ≤
      Real.sqrt κ • (ofFullBlockMat (geoMean AG (RR * AG⁻¹ * RR))).lowerRight := by
    have h := lowerRightMono hMhi
    rwa [lowerRight_smul] at h
  set LF := (ofFullBlockMat (geoMean AF (RR * AF⁻¹ * RR))).lowerRight
  set LG := (ofFullBlockMat (geoMean AG (RR * AG⁻¹ * RR))).lowerRight
  have hmF : (LF⁻¹).PosDef := hLF.inv
  have hmG : (LG⁻¹).PosDef := hLG.inv
  have hstep1 : LF⁻¹ ≤ Real.sqrt κ • LG⁻¹ := by
    have h := inv_le_inv_of_le (hLG.smul (inv_pos.mpr hsk)) hLF hLlo
    rwa [inv_smul_of_posDef hLG (inv_pos.mpr hsk).ne', inv_inv] at h
  have hstep2 : (Real.sqrt κ)⁻¹ • LG⁻¹ ≤ LF⁻¹ := by
    have h := inv_le_inv_of_le hLF (hLG.smul hsk) hLhi
    rwa [inv_smul_of_posDef hLG hsk.ne'] at h
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

/-- A18 (kernel). The entry radius of the reference block itself :
`Cgeom` depends on `d` alone. -/
theorem explicitCanonicalMetric_refBlock_projectiveDistance_le (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ E : BlockMat d, IsSymmetricBlockMat E → Book.Ch02.BlockPosDef E →
        BlockMatLoewnerLE
          (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
            toFullBlockMat (blockSwap d))) E →
        projectiveDistance (1 : Mat d) (explicitCanonicalMetric E) ≤
          Cgeom * Real.log (2 + 4 * aspectRatio E) := by
  have : NeZero d := ⟨by omega⟩
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro E hsymm hpos horder
  have hAE : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hsymm hpos
  have hSE : (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
      toFullBlockMat (blockSwap d)).PosDef := Geometry.swapConj_inv_posDef hsymm hpos
  have hlam0 : 0 < lambdaRef E := Analysis.lambdaRef_pos hsymm hpos
  have hLam0 : 0 < bigLambdaRef E := Analysis.bigLambdaRef_pos hsymm hpos
  have hAsp : 1 ≤ aspectRatio E := Analysis.one_le_aspectRatio hsymm hpos horder
  have hlr := Analysis.swapConj_lowerRight hsymm hpos
  have hElr : E.lowerRight.PosDef := posDef_lowerRight hsymm hpos
  rw [explicitCanonicalMetric_eq_geoMean E]
  set AE : FullBlockMat d := toFullBlockMat E
  set SE : FullBlockMat d := toFullBlockMat (blockSwap d) * AE⁻¹ * toFullBlockMat (blockSwap d)
  have hSEsymm : IsSymmetricBlockMat (ofFullBlockMat SE) :=
    (Analysis.toFullBlockMat_isHermitian_iff _).1
      (by rw [toFullBlockMat_ofFullBlockMat]; exact hSE.isHermitian)
  have hord : SE ≤ AE := by
    have h := fullLE_of_block hSEsymm hsymm horder
    rwa [toFullBlockMat_ofFullBlockMat] at h
  -- the balance chain `E♯ ≤ M(E) ≤ E`
  have hchain1 : SE ≤ geoMean AE SE := by
    have h := geoMean_mono hSE hAE hSE hSE hord (le_refl SE)
    rwa [geoMean_self hSE] at h
  have hchain2 : geoMean AE SE ≤ AE := by
    have h := geoMean_mono hAE hAE hSE hAE (le_refl AE) hord
    rwa [geoMean_self hAE] at h
  have hL1 := lowerRightMono hchain1
  have hL2 := lowerRightMono hchain2
  rw [ofFullBlockMat_toFullBlockMat] at hL2
  rw [hlr] at hL1
  set L := (ofFullBlockMat (geoMean AE SE)).lowerRight
  have hLpos : L.PosDef := lowerRightPosDef (geoMeanPosDef hAE hSE)
  have hsig : (schurSigma E).PosDef := by
    have h := lowerRightPosDef hSE
    rw [hlr] at h
    simpa using h.inv
  -- invert the two block comparisons
  have hup : L⁻¹ ≤ schurSigma E := by
    have h := inv_le_inv_of_le hsig.inv hLpos hL1
    rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hsig)] at h
  have hlow : E.lowerRight⁻¹ ≤ L⁻¹ := inv_le_inv_of_le hLpos hElr hL2
  -- the two scalar bounds
  have hDle : E.lowerRight ≤ specBound E.lowerRight • (1 : Mat d) :=
    (matLE_iff hElr.isHermitian (hermSmulOne _)).2
      (matLoewnerLE_specBound_smul_one E.lowerRight)
  have hspec : 0 < specBound E.lowerRight := by
    have : lambdaRef E = (specBound E.lowerRight)⁻¹ := rfl
    rw [this] at hlam0
    exact inv_pos.mp hlam0
  have hlam : lambdaRef E • (1 : Mat d) ≤ E.lowerRight⁻¹ := by
    have h := inv_le_inv_of_le hElr (Matrix.PosDef.one.smul hspec) hDle
    rwa [inv_smul_of_posDef Matrix.PosDef.one hspec.ne', inv_one] at h
  have hLam : L⁻¹ ≤ bigLambdaRef E • (1 : Mat d) :=
    hup.trans (schurSigma_le_bigLambdaRef hsymm hpos)
  have hfin := projectiveDistance_le_of_sandwich (d := d) Matrix.PosDef.one hLpos.inv hlam0
    ((matLE_iff (hermSmulOne _) hLpos.inv.isHermitian).1 (hlam.trans hlow))
    ((matLE_iff hLpos.inv.isHermitian (hermSmulOne _)).1 hLam)
  have hasp : bigLambdaRef E / lambdaRef E = aspectRatio E := rfl
  rw [hasp] at hfin
  refine hfin.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  exact Real.log_le_log (lt_of_lt_of_le zero_lt_one hAsp) (by linarith only [hAsp])

/-- A19. The entry-radius estimate (`p.initial.fixed.grid.scale`): a block sandwiched between
`½𝐑𝐄⁻¹𝐑` and `2𝐄` has canonical metric within `C(d) log(2+4Π)` of `Id`. -/
theorem entry_radius (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ (E A : BlockMat d), IsSymmetricBlockMat E → Book.Ch02.BlockPosDef E →
        BlockMatLoewnerLE
          (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
            toFullBlockMat (blockSwap d))) E →
        (toFullBlockMat A).PosDef →
        BlockMatLoewnerLE
          (blockScale (1 / 2)
            (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
              toFullBlockMat (blockSwap d)))) A →
        BlockMatLoewnerLE A (blockScale 2 E) →
        projectiveDistance (1 : Mat d) (explicitCanonicalMetric A) ≤
          Cgeom * Real.log (2 + 4 * aspectRatio E) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cgeom_ref, hCgeom_ref_pos, href⟩ := explicitCanonicalMetric_refBlock_projectiveDistance_le d hd
  refine ⟨Cgeom_ref + 1, by linarith only [hCgeom_ref_pos], ?_⟩
  intro E A hsymm hpos horder hAfull hlow hhigh
  have hAsymm : IsSymmetricBlockMat A :=
    (Analysis.toFullBlockMat_isHermitian_iff A).mp hAfull.isHermitian
  have hApos : Book.Ch02.BlockPosDef A := blockPosDef_of_toFullBlockMat_posDef A hAfull
  have hPi : 1 ≤ aspectRatio E := Analysis.one_le_aspectRatio hsymm hpos horder
  have hPi_pos : 0 < aspectRatio E := lt_of_lt_of_le zero_lt_one hPi
  have hscale_mono : ∀ {X Y : BlockMat d} {c : ℝ}, 0 ≤ c →
      BlockMatLoewnerLE X Y →
      BlockMatLoewnerLE (blockScale c X) (blockScale c Y) := by
    intro X Y c hc hXY V
    rw [Source.quadratic_blockScale, Source.quadratic_blockScale]
    exact mul_le_mul_of_nonneg_left (hXY V) hc
  have hscale_scale : ∀ (X : BlockMat d) (a b : ℝ),
      blockScale a (blockScale b X) = blockScale (a * b) X := by
    intro X a b
    cases X
    simp [blockScale, smul_smul]
  have hRle : BlockMatLoewnerLE E
      (blockScale (6 * aspectRatio E)
        (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
          toFullBlockMat (blockSwap d)))) :=
    Analysis.refBlock_le_six_aspectRatio_smul_swapConj hsymm hpos horder
  have hc_pos : 0 < (12 * aspectRatio E)⁻¹ :=
    inv_pos.mpr (mul_pos (by norm_num) hPi_pos)
  have hlow' : BlockMatLoewnerLE (blockScale ((12 * aspectRatio E)⁻¹) E) A := by
    refine (hscale_mono hc_pos.le hRle).trans ?_
    rw [hscale_scale]
    convert hlow using 1
    field_simp [hPi_pos.ne']
    ring_nf
  have hκ : 1 ≤ 24 * aspectRatio E := by linarith only [hPi]
  have hhi' : BlockMatLoewnerLE A
      (blockScale ((24 * aspectRatio E) * (12 * aspectRatio E)⁻¹) E) := by
    refine hhigh.trans ?_
    apply Source.blockScale_le_blockScale_of_pos hpos
    have hden : 12 * aspectRatio E ≠ 0 := mul_ne_zero (by norm_num) hPi_pos.ne'
    field_simp [hden]
    norm_num
  have hsand := explicitCanonicalMetric_projectiveDistance_le_of_sandwich d hd A E hAsymm hApos hsymm hpos
    ((12 * aspectRatio E)⁻¹) (24 * aspectRatio E) hc_pos hκ hlow' hhi'
  have hAE : projectiveDistance (explicitCanonicalMetric E) (explicitCanonicalMetric A) ≤
      Real.log (2 + 4 * aspectRatio E) := by
    rw [Geometry.projectiveDistance_symm (Geometry.explicitCanonicalMetric_posDef hsymm hpos)
      (Geometry.explicitCanonicalMetric_posDef hAsymm hApos)]
    exact hsand.trans (half_log_aspect_le (aspectRatio E) hPi)
  have htri := Geometry.projectiveDistance_triangle (Geometry.one_posDef d)
    (Geometry.explicitCanonicalMetric_posDef hsymm hpos) (Geometry.explicitCanonicalMetric_posDef hAsymm hApos)
  have hrefE := href E hsymm hpos horder
  calc
    projectiveDistance (1 : Mat d) (explicitCanonicalMetric A)
        ≤ projectiveDistance (1 : Mat d) (explicitCanonicalMetric E) +
            projectiveDistance (explicitCanonicalMetric E) (explicitCanonicalMetric A) := htri
    _ ≤ Cgeom_ref * Real.log (2 + 4 * aspectRatio E) +
          Real.log (2 + 4 * aspectRatio E) := add_le_add hrefE hAE
    _ = (Cgeom_ref + 1) * Real.log (2 + 4 * aspectRatio E) := by ring

end

end HCPolySupport.HighContrast.Multiscale
