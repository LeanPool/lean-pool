/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioOrder
public import LeanPool.HighContrastHomogenization.Geometry.SchurData
public import LeanPool.HighContrastHomogenization.Geometry.SizeAlignment
public import LeanPool.HighContrastHomogenization.Provider.Initialization.Reference
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.SchurHelpers

/-!
# High-contrast homogenization: Provider.Initialization.ReferenceComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The reference comparison `κ_𝐄 ≤ 6 Π`

The factor-six reference-block comparison states `κ_𝐄 ≤ 1 + 6(Θ - 1) ≤ 6 Π` for
a reference block whose sharp it dominates.  The printed derivation routes
through the display preceding (2.98) of Armstrong–Kuusi, an inequality about the
*un-corrected* Schur block; the route taken here reaches the final bound
`κ_𝐄 ≤ 6 Π` directly from the reference aspect ratio, and it is elementary.

Write `(σ, σ_*, k)` for the Schur data of `𝐄`, so that

* the quadratic form of `𝐄` at `(x, y)` is `⟨σ x, x⟩ + ⟨σ_*⁻¹ (y - k x), y - k x⟩`;
* the sharp has Schur data `(σ_*, σ, -kᵗ)`, so its quadratic form at `(x, y)` is
  `⟨σ_* x, x⟩ + ⟨σ⁻¹ (y + kᵗ x), y + kᵗ x⟩`.

Three inputs are used, all already available.  The ordering `𝐄^♯ ≤ 𝐄` gives
`σ_* ≤ σ` on the lower-right blocks.  The skew matrix realizing `Λ_0` gives
`σ + mᵗ σ_*⁻¹ m ≤ Λ_0 · I` with `m = k - h`, and `I ≤ |σ_*⁻¹| σ_*` turns that
into `σ + mᵗ σ_*⁻¹ m ≤ Π σ_*`, whence both `σ ≤ Π σ_*` and
`mᵗ σ_*⁻¹ m ≤ (Π - 1) σ_*`.  Transposition preserves the second bound, and the
symmetric part `K = k + kᵗ = m + mᵗ` therefore satisfies
`K σ_*⁻¹ K ≤ 4(Π - 1) σ_*`.

The comparison is then one application of Young's inequality with the weight
five: writing `w = y + kᵗ x`, so that `y - k x = w - K x`,

`⟨σ_*⁻¹ (w - K x), w - K x⟩ ≤ 6 ⟨σ_*⁻¹ w, w⟩ + (6/5) ⟨σ_*⁻¹ K x, K x⟩`,

and the three displayed bounds turn the left side of the comparison into
`(6Π - (Π/5 + 24/5)) ⟨σ_* x, x⟩ + 6 ⟨σ_*⁻¹ w, w⟩`, which is below
`6Π (⟨σ_* x, x⟩ + ⟨σ⁻¹ w, w⟩)` because `σ_*⁻¹ ≤ Π σ⁻¹`.  The slack
`Π/5 + 24/5` is why the printed constant six survives the cruder route.
-/

namespace HCPolySupport
namespace HighContrast
namespace Initialization

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Quadratic forms of a Schur block -/

private theorem quad_fromBlocks_diag (a t : Mat d) (x y : Vec d) :
    Sum.elim x y ⬝ᵥ (Matrix.fromBlocks a 0 0 t : FullBlockMat d) *ᵥ Sum.elim x y =
      x ⬝ᵥ a *ᵥ x + y ⬝ᵥ t *ᵥ y := by
  rw [Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Matrix.mulVec, Finset.mul_sum]

private theorem mulVec_fullBlockShear (h : Mat d) (x y : Vec d) :
    (fullBlockShear h) *ᵥ Sum.elim x y = Sum.elim x (h *ᵥ x + y) := by
  rw [fullBlockShear, Matrix.fromBlocks_mulVec]
  funext α
  cases α <;> simp

/-- **The quadratic form of a Schur block.**  At `(x, y)` the block
`G_{-c}ᵗ diag(a, b⁻¹) G_{-c}` reads `⟨a x, x⟩ + ⟨b⁻¹ (y - c x), y - c x⟩`. -/
theorem dotProduct_mulVec_schurBlock (a b c : Mat d) (x y : Vec d) :
    Sum.elim x y ⬝ᵥ (schurBlock a b c) *ᵥ Sum.elim x y =
      x ⬝ᵥ a *ᵥ x + (y - c *ᵥ x) ⬝ᵥ b⁻¹ *ᵥ (y - c *ᵥ x) := by
  have hshear : (fullBlockShear (-c)) *ᵥ Sum.elim x y = Sum.elim x (y - c *ᵥ x) := by
    rw [mulVec_fullBlockShear, Matrix.neg_mulVec]
    congr 1
    abel
  rw [schurBlock, quad_conj, hshear, quad_fromBlocks_diag]

/-! ## Two matrix inequalities -/

/-- **Young's inequality at weight five** for the semi-inner product of a
positive semidefinite matrix. -/
private theorem dotProduct_mulVec_sub_le {X : Mat d} (hX : X.PosSemidef) (u v : Vec d) :
    (u - v) ⬝ᵥ X *ᵥ (u - v) ≤ 6 * (u ⬝ᵥ X *ᵥ u) + 6 / 5 * (v ⬝ᵥ X *ᵥ v) := by
  have hXsymm : Xᵀ = X := by
    rw [← conjTranspose_eq_transpose']; exact hX.isHermitian
  have hcross : v ⬝ᵥ X *ᵥ u = u ⬝ᵥ X *ᵥ v := by
    rw [dotProduct_mulVec_symm hXsymm v u, dotProduct_comm]
  have hpos := hX.dotProduct_mulVec_nonneg ((5 : ℝ) • u + v)
  simp only [star_trivial] at hpos
  have hexp1 : ((5 : ℝ) • u + v) ⬝ᵥ X *ᵥ ((5 : ℝ) • u + v) =
      25 * (u ⬝ᵥ X *ᵥ u) + 10 * (u ⬝ᵥ X *ᵥ v) + v ⬝ᵥ X *ᵥ v := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hcross]
    ring
  have hexp2 : (u - v) ⬝ᵥ X *ᵥ (u - v) =
      u ⬝ᵥ X *ᵥ u - 2 * (u ⬝ᵥ X *ᵥ v) + v ⬝ᵥ X *ᵥ v := by
    simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, hcross]
    ring
  rw [hexp1] at hpos
  rw [hexp2]
  linarith only [hpos]

/-! ## The Schur form of a symmetric positive block -/

/-- **The Schur form.**  A symmetric positive definite doubled block is the Schur
form of its own Schur data. -/
theorem toFullBlockMat_eq_schurBlock {E : BlockMat d} (hsymm : IsSymmetricBlockMat E)
    (hpos : Book.Ch02.BlockPosDef E) :
    toFullBlockMat E = schurBlock (schurSigma E) (schurSigmaStar E) (schurSkew E) := by
  have hdet : IsUnit E.lowerRight.det := isUnit_det_lowerRight hpos
  have hstar : (schurSigmaStar E)⁻¹ = E.lowerRight := schurSigmaStar_inv E hdet
  have hLRsymm : (E.lowerRight)ᵀ = E.lowerRight := by
    ext i j
    exact hsymm (Sum.inr j) (Sum.inr i)
  have hUR : E.upperRight = (E.lowerLeft)ᵀ := by
    ext i j
    exact hsymm (Sum.inl i) (Sum.inr j)
  have hkT : (schurSkew E)ᴴ = -((E.lowerLeft)ᵀ * E.lowerRight⁻¹) := by
    rw [conjTranspose_eq_transpose', schurSkew, Matrix.transpose_neg,
      Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hLRsymm]
  rw [schurBlock_eq, hstar, toFullBlockMat_eq_fromBlocks, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [schurSigma, conjTranspose_eq_transpose']
    simp [matTranspose]
  · rw [hkT, hUR, Matrix.neg_mul, neg_neg, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  · rw [schurSkew, Matrix.mul_neg, neg_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]

/-! ## The reference comparison -/

/-- **The factor-six reference-block comparison** `κ_𝐄 ≤ 6 Π`, for a symmetric
positive doubled block dominating its own sharp. -/
theorem kappaRef_le_six_mul_aspectRatio [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E) :
    kappaRef E ≤ 6 * aspectRatio E := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  -- the Schur data and its positivity
  have hEfull : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hsymm hpos
  have hdet : IsUnit E.lowerRight.det := isUnit_det_lowerRight hpos
  have hTpd : (E.lowerRight).PosDef :=
    posDef_of_posSemidef_of_isUnit (posSemidef_lowerRight hsymm hpos)
      ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  have hstarPd : (schurSigmaStar E).PosDef := hTpd.inv
  have hstarInv : (schurSigmaStar E)⁻¹ = E.lowerRight := schurSigmaStar_inv E hdet
  have hform : toFullBlockMat E =
      schurBlock (schurSigma E) (schurSigmaStar E) (schurSkew E) :=
    toFullBlockMat_eq_schurBlock hsymm hpos
  have hEschur : (schurBlock (schurSigma E) (schurSigmaStar E) (schurSkew E)).PosDef := by
    rw [← hform]; exact hEfull
  have hsPd : (schurSigma E).PosDef := posDef_of_posDef_schurBlock hstarPd hEschur
  have hsharpFull : (toFullBlockMat (blockSharp E)).PosDef := by
    rw [toFullBlockMat_blockSharp]; exact posDef_fullBlockSharp hEfull
  have hsharpSymm : IsSymmetricBlockMat (blockSharp E) :=
    isSymmetricBlockMat_of_posSemidef hsharpFull.posSemidef
  have hsharpForm : toFullBlockMat (blockSharp E) =
      schurBlock (schurSigmaStar E) (schurSigma E) (-(schurSkew E)ᴴ) := by
    rw [toFullBlockMat_blockSharp, hform, fullBlockSharp_schurBlock hsPd hstarPd]
  -- the ordering of the two Schur blocks
  have hle : toFullBlockMat (blockSharp E) ≤ toFullBlockMat E :=
    le_of_blockMatLoewnerLE hsharpSymm hsymm hsharp
  have horder : schurSigmaStar E ≤ schurSigma E := by
    have h22 := toBlocks₂₂_mono hle
    rw [hsharpForm, hform, toBlocks₂₂_schurBlock, toBlocks₂₂_schurBlock] at h22
    have h := inv_le_inv_of_le hsPd.inv hstarPd.inv h22
    rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hstarPd),
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hsPd)] at h
  have hPi1 : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_schurSigmaStar_le hsymm hpos (matLoewnerLE_of_le horder)
  have hPipos : (0 : ℝ) < aspectRatio E := lt_of_lt_of_le zero_lt_one hPi1
  -- the skew matrix realizing the reference constant
  obtain ⟨h0, hskew, hLam⟩ := exists_isSkewMat_bigLambdaRef_eq hpos
  set m : Mat d := schurSkew E - h0 with hmdef
  have hTherm : (E.lowerRight)ᴴ = E.lowerRight := hTpd.isHermitian
  have hcorrEq : skewCorrectedForm E h0 = schurSigma E + mᴴ * E.lowerRight * m := by
    rw [conjTranspose_eq_transpose']
    rfl
  have hchain : MatLoewnerLE (skewCorrectedForm E h0)
      (aspectRatio E • schurSigmaStar E) := by
    have hcorr : MatLoewnerLE (skewCorrectedForm E h0) (bigLambdaRef E • (1 : Mat d)) := by
      rw [hLam]; exact matLoewnerLE_specBound_smul_one _
    have hone : MatLoewnerLE (1 : Mat d) (specBound E.lowerRight • schurSigmaStar E) :=
      matLoewnerLE_one_specBound_smul_schurSigmaStar hsymm hpos
    have hstep := hcorr.trans (matLoewnerLE_smul (bigLambdaRef_nonneg E) hone)
    rwa [smul_smul, ← aspectRatio_eq_bigLambdaRef_mul_specBound] at hstep
  have hcorrPS : (mᴴ * E.lowerRight * m).PosSemidef :=
    hTpd.posSemidef.conjTranspose_mul_mul_same m
  have hPiLe : schurSigma E + mᴴ * E.lowerRight * m ≤ aspectRatio E • schurSigmaStar E := by
    refine le_of_matLoewnerLE ?_ ?_ (by rwa [hcorrEq] at hchain)
    · exact hsPd.isHermitian.add hcorrPS.isHermitian
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hstarPd.isHermitian]
      simp
  -- the two normalized quadratic bounds on the Schur skew block
  have hmT : mᴴ * E.lowerRight * m ≤ (aspectRatio E - 1) • schurSigmaStar E := by
    refine Matrix.le_iff.mpr ?_
    have hsum := (Matrix.le_iff.mp hPiLe).add (Matrix.le_iff.mp horder)
    have hrw : aspectRatio E • schurSigmaStar E -
          (schurSigma E + mᴴ * E.lowerRight * m) + (schurSigma E - schurSigmaStar E) =
        (aspectRatio E - 1) • schurSigmaStar E - mᴴ * E.lowerRight * m := by
      rw [sub_smul, one_smul]; abel
    rwa [hrw] at hsum
  have hmT' : m * E.lowerRight * mᴴ ≤ (aspectRatio E - 1) • schurSigmaStar E := by
    rw [schurSigmaStar] at hmT ⊢
    exact conj_transpose_le_of_conj_le hTpd (by linarith only [hPi1]) hmT
  -- the symmetric part of the Schur skew block
  have hKm : schurSkew E + (schurSkew E)ᴴ = m + mᴴ := by
    have hh0 : (h0)ᴴ = -h0 := by
      rw [conjTranspose_eq_transpose']
      exact hskew
    rw [hmdef, Matrix.conjTranspose_sub, hh0]
    abel
  have hK : (schurSkew E + (schurSkew E)ᴴ)ᴴ * E.lowerRight *
      (schurSkew E + (schurSkew E)ᴴ) ≤
      (4 * (aspectRatio E - 1)) • schurSigmaStar E := by
    rw [hKm]
    refine Matrix.le_iff.mpr ?_
    have hbound := Matrix.le_iff.mp (conj_add_le hTpd.posSemidef m mᴴ)
    have h1 := Matrix.le_iff.mp hmT
    have h2 := Matrix.le_iff.mp hmT'
    have hsum := hbound.add (h1.add (h1.add (h2.add h2)))
    have hrw : (mᴴ * E.lowerRight * m + mᴴ * E.lowerRight * m +
            ((mᴴ)ᴴ * E.lowerRight * mᴴ + (mᴴ)ᴴ * E.lowerRight * mᴴ) -
          (m + mᴴ)ᴴ * E.lowerRight * (m + mᴴ)) +
        (((aspectRatio E - 1) • schurSigmaStar E - mᴴ * E.lowerRight * m) +
          (((aspectRatio E - 1) • schurSigmaStar E - mᴴ * E.lowerRight * m) +
            (((aspectRatio E - 1) • schurSigmaStar E - m * E.lowerRight * mᴴ) +
              ((aspectRatio E - 1) • schurSigmaStar E - m * E.lowerRight * mᴴ)))) =
        (4 * (aspectRatio E - 1)) • schurSigmaStar E -
          (m + mᴴ)ᴴ * E.lowerRight * (m + mᴴ) := by
      rw [Matrix.conjTranspose_conjTranspose]
      module
    rwa [hrw] at hsum
  -- the upper Schur block and the reversed comparison
  have hs : schurSigma E ≤ aspectRatio E • schurSigmaStar E := by
    refine le_trans (Matrix.le_iff.mpr ?_) hPiLe
    have hrw : schurSigma E + mᴴ * E.lowerRight * m - schurSigma E =
        mᴴ * E.lowerRight * m := by abel
    rw [hrw]
    exact hcorrPS
  have hTs : E.lowerRight ≤ aspectRatio E • (schurSigma E)⁻¹ := by
    have hsmulPd : (aspectRatio E • schurSigmaStar E).PosDef := hstarPd.smul hPipos
    have hinv : (aspectRatio E • schurSigmaStar E)⁻¹ =
        (aspectRatio E)⁻¹ • E.lowerRight := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        mul_inv_cancel₀ (ne_of_gt hPipos), one_smul, schurSigmaStar,
        Matrix.nonsing_inv_mul _ hdet]
    have hstep := inv_le_inv_of_le hsPd hsmulPd hs
    rw [hinv] at hstep
    have h := smul_le_smul_of_le (c := aspectRatio E) hPipos.le hstep
    rwa [smul_smul, mul_inv_cancel₀ (ne_of_gt hPipos), one_smul] at h
  -- the comparison itself
  have hsharpPd : Book.Ch02.BlockPosDef (blockSharp E) :=
    (blockPosDef_iff_posDef hsharpSymm).mpr hsharpFull
  rw [kappaRef, blockSize_eq_relSize hsymm hsharpSymm hsharpPd hEfull.posSemidef]
  refine (relSize_le_iff hEfull.posSemidef hsharpFull (by linarith only [hPi1])).mpr ?_
  refine le_of_dotProduct_mulVec_le hEfull.isHermitian ?_ fun v => ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hsharpFull.isHermitian]
    simp
  · rw [← elim_comp v]
    set x : Vec d := v ∘ Sum.inl with hxdef
    set y : Vec d := v ∘ Sum.inr with hydef
    rw [hform, dotProduct_mulVec_schurBlock, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, hsharpForm, dotProduct_mulVec_schurBlock, hstarInv]
    set w : Vec d := y - (-(schurSkew E)ᴴ) *ᵥ x with hwdef
    have hsplit : y - (schurSkew E) *ᵥ x =
        w - (schurSkew E + (schurSkew E)ᴴ) *ᵥ x := by
      rw [hwdef, Matrix.add_mulVec, Matrix.neg_mulVec]
      abel
    rw [hsplit]
    -- the four quadratic bounds
    have hA1 : x ⬝ᵥ (schurSigma E) *ᵥ x ≤
        aspectRatio E * (x ⬝ᵥ (schurSigmaStar E) *ᵥ x) := by
      have h := dotProduct_mulVec_le_of_le hs x
      rwa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    have hA2 := dotProduct_mulVec_sub_le hTpd.posSemidef w
      ((schurSkew E + (schurSkew E)ᴴ) *ᵥ x)
    have hA3 : ((schurSkew E + (schurSkew E)ᴴ) *ᵥ x) ⬝ᵥ E.lowerRight *ᵥ
        ((schurSkew E + (schurSkew E)ᴴ) *ᵥ x) ≤
        4 * (aspectRatio E - 1) * (x ⬝ᵥ (schurSigmaStar E) *ᵥ x) := by
      have h := dotProduct_mulVec_le_of_le hK x
      rw [quad_conj, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
      exact h
    have hA4 : w ⬝ᵥ E.lowerRight *ᵥ w ≤
        aspectRatio E * (w ⬝ᵥ (schurSigma E)⁻¹ *ᵥ w) := by
      have h := dotProduct_mulVec_le_of_le hTs w
      rwa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    have hSx : (0 : ℝ) ≤ x ⬝ᵥ (schurSigmaStar E) *ᵥ x := by
      simpa using hstarPd.posSemidef.dotProduct_mulVec_nonneg x
    have hIw : (0 : ℝ) ≤ w ⬝ᵥ (schurSigma E)⁻¹ *ᵥ w := by
      simpa using hsPd.inv.posSemidef.dotProduct_mulVec_nonneg w
    nlinarith only [hA1, hA2, hA3, hA4, mul_nonneg hPipos.le hSx, hSx, hIw,
      hPi1]

/-- **The reference comparison under the coarse ellipticity assumption.**  At a
probability law the reference block of `e.coarse.ellipticity` dominates its own
sharp, so the factor-six reference-block comparison applies to it. -/
theorem kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    kappaRef E ≤ 6 * aspectRatio E :=
  kappaRef_le_six_mul_aspectRatio hdag.refBlock_isSymm hdag.refBlock_posDef
    (blockMatLoewnerLE_blockSharp_reference hdag)

end

end Initialization
end HighContrast
end HCPolySupport
