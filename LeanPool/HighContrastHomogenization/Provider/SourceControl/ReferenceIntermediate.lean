/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Initialization.ReferenceComparison
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.SchurHelpers

/-!
# High-contrast homogenization: Provider.SourceControl.ReferenceIntermediate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The reference intermediate `κ_𝐄 ≤ 1 + 6(Θ - 1) ≤ 6 Π`

The factor-six reference-block comparison states the chain
`κ_𝐄 ≤ 1 + 6(Θ - 1) ≤ 6 Π` for a reference block dominating its own sharp.  The
endpoint `κ_𝐄 ≤ 6 Π` is proved in
`HCPoly.Provider.Initialization.ReferenceComparison`; this file proves the two
remaining links, at the *intrinsic* contrast `Θ = refContrast 𝐄`.

The printed derivation of the first link routes through the display preceding
(2.98) of Armstrong–Kuusi, which fails at large contrast (a counterexample exists at
contrast nine, where both of its displays are exceeded).  The route
taken here is different, and elementary.  Write `(σ, σ_*, k)` for the Schur data
of `𝐄` and `T = σ_*⁻¹` for its lower-right block, so that at `(x, y)`

* the quadratic form of `𝐄` is `⟨σ x, x⟩ + ⟨T (y - k x), y - k x⟩`;
* the quadratic form of `𝐄^♯` is `⟨σ_* x, x⟩ + ⟨σ⁻¹ (y + kᵗ x), y + kᵗ x⟩`.

Fix a skew `h` with `σ + mᵗ T m ≤ t σ_*`, put `m = k - h` and
`K = k + kᵗ = m + mᵗ`, and write `w = y + kᵗ x`, so that `y - k x = w - K x`.
Exactly as in the endpoint proof, the ordering `𝐄^♯ ≤ 𝐄` gives `σ_* ≤ σ`, hence
`1 ≤ t`, and then the three normalized bounds

`σ ≤ t σ_*`,  `Kᵗ T K ≤ 4(t - 1) σ_*`,  `T ≤ t σ⁻¹`.

The cross term `⟨T w, K x⟩` is *not* discarded by Young's inequality here.  Doing
so — the endpoint's route — bounds the reading of the `w` coordinate by `6 t`,
and the target `1 + 6(t - 1) = 6t - 5` is strictly below that; no admissible
Young weight repairs it below `t = 5`, since a weight `1 + ε` on `⟨T w, w⟩` costs
`4(1 + 1/ε)(t-1)` on `⟨σ_* x, x⟩` and the two constraints
`(1+ε) t ≤ 6t - 5` and `t + 4(1 + 1/ε)(t-1) ≤ 6t - 5` are compatible only for
`ε ≥ 4`, hence only for `t ≥ 5`.  The cross term is bounded instead by the sharp
ordering itself, read at the rescaled vector whose second Schur coordinate is
`-5 w`:

`⟨σ_* x, x⟩ + 25 ⟨σ⁻¹ w, w⟩ ≤ ⟨σ x, x⟩ + 25 ⟨T w, w⟩ + 10 ⟨T w, K x⟩ + ⟨T K x, K x⟩`.

The weight five is the unique one at which the resulting linear combination of
the four bounds reproduces `1 + 6(t - 1)` on *both* coordinates at once: with
weight `1/γ` the two readings are `t + (t-1)/γ` and `(1+γ)(5t - 4) - γ`, and
`γ = 1/5` is the only value making both equal `6t - 5`.  The comparison is
therefore exact, with no slack anywhere; at `t = 1` it degenerates to
`𝐄 ≤ 𝐄^♯`, which is the sharp ordering read backwards.

The second link is the printed chain for `Π`: at the `Λ_0`-realizing skew,
`σ + mᵗ T m ≤ Λ_0 · I ≤ Λ_0 |σ_*⁻¹| σ_* = Π σ_*`, so `Π` is admissible for the
infimum defining `Θ`, whence `Θ ≤ Π`.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Initialization

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## The intrinsic contrast as an infimum -/

/-- **The intrinsic contrast is realized in Loewner form.**  On a symmetric
positive definite doubled block some skew matrix attains the infimum defining
`Θ`, as a Loewner bound against `σ_*`. -/
theorem exists_isSkewMat_matLoewnerLE_refContrast_smul {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) :
    ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE (skewCorrectedForm E h) (refContrast E • schurSigmaStar E) :=
  exists_isSkewMat_matLoewnerLE_sInf_smul (H := E) (N := schurSigmaStar E)
    (quadratic_pos_lowerRight hpos)
    (exists_coercivity_of_quadratic_pos (quadratic_pos_schurSigmaStar hsymm hpos))

/-- **The `Π` chain.**  At the `Λ_0`-realizing skew the skew-corrected Schur form
is below `Π σ_*`: this is `σ + mᵗ σ_*⁻¹ m ≤ Λ_0 I ≤ Λ_0 |σ_*⁻¹| σ_*`. -/
theorem exists_isSkewMat_matLoewnerLE_aspectRatio_smul {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) :
    ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE (skewCorrectedForm E h) (aspectRatio E • schurSigmaStar E) := by
  obtain ⟨h0, hskew, hLam⟩ := exists_isSkewMat_bigLambdaRef_eq hpos
  refine ⟨h0, hskew, ?_⟩
  have hcorr : MatLoewnerLE (skewCorrectedForm E h0) (bigLambdaRef E • (1 : Mat d)) := by
    rw [hLam]; exact matLoewnerLE_specBound_smul_one _
  have hone : MatLoewnerLE (1 : Mat d) (specBound E.lowerRight • schurSigmaStar E) :=
    matLoewnerLE_one_specBound_smul_schurSigmaStar hsymm hpos
  have hstep := hcorr.trans (matLoewnerLE_smul (bigLambdaRef_nonneg E) hone)
  rwa [smul_smul, ← aspectRatio_eq_bigLambdaRef_mul_specBound] at hstep

/-- **The intrinsic contrast is below the aspect ratio**, `Θ ≤ Π`: the second
link of the factor-six reference-block comparison.  The aspect ratio is an admissible
Loewner scaling for the infimum defining the contrast. -/
theorem refContrast_le_aspectRatio {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) :
    refContrast E ≤ aspectRatio E := by
  obtain ⟨h, hskew, hle⟩ := exists_isSkewMat_matLoewnerLE_aspectRatio_smul hsymm hpos
  exact blockContrast_le (aspectRatio_nonneg E) hskew hle

/-! ## The Schur ordering -/

/-- **The Schur ordering from the sharp ordering.**  A symmetric positive
doubled block dominating its own sharp has ordered symmetric Schur blocks,
`σ_* ≤ σ`: the lower-right blocks of the two Schur forms are `σ⁻¹ ≤ σ_*⁻¹`. -/
theorem schurSigmaStar_le_schurSigma {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E) :
    schurSigmaStar E ≤ schurSigma E := by
  have hEfull : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hsymm hpos
  have hdet : IsUnit E.lowerRight.det := isUnit_det_lowerRight hpos
  have hTpd : (E.lowerRight).PosDef :=
    posDef_of_posSemidef_of_isUnit (posSemidef_lowerRight hsymm hpos)
      ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  have hstarPd : (schurSigmaStar E).PosDef := hTpd.inv
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
  have h22 := toBlocks₂₂_mono (le_of_blockMatLoewnerLE hsharpSymm hsymm hsharp)
  rw [hsharpForm, hform, toBlocks₂₂_schurBlock, toBlocks₂₂_schurBlock] at h22
  have h := inv_le_inv_of_le hsPd.inv hstarPd.inv h22
  rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hstarPd),
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hsPd)] at h

/-- **An admissible scaling is at least one** under the Schur ordering: from
`σ_* ≤ σ ≤ σ + mᵗ T m ≤ t σ_*` and the positivity of `σ_*`. -/
theorem one_le_of_matLoewnerLE_skewCorrectedForm [NeZero d] {E : BlockMat d} {t : ℝ}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (horder : MatLoewnerLE (schurSigmaStar E) (schurSigma E)) {h0 : Mat d}
    (hchain : MatLoewnerLE (skewCorrectedForm E h0) (t • schurSigmaStar E)) :
    1 ≤ t := by
  set e : Vec d := Pi.single ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ (1 : ℝ) with hedef
  have hne : e ≠ 0 := by
    intro hc
    have h1 : e ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ =
        (0 : Vec d) ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ := by rw [hc]
    rw [hedef, Pi.single_eq_same] at h1
    exact one_ne_zero h1
  have hepos : 0 < vecDot e (matVecMul (schurSigmaStar E) e) :=
    quadratic_pos_schurSigmaStar hsymm hpos e hne
  have hsm : vecDot e (matVecMul (t • schurSigmaStar E) e) =
      t * vecDot e (matVecMul (schurSigmaStar E) e) := by
    rw [smul_matVecMul, vecDot_smul_right]
  have h1 := horder e
  have h2 := (matLoewnerLE_schurSigma_skewCorrectedForm hpos h0) e
  have h3 := hchain e
  rw [hsm] at h3
  refine le_of_mul_le_mul_right ?_ hepos
  rw [one_mul]
  linarith only [h1, h2, h3]

/-! ## The intermediate comparison -/

/-- **The reference intermediate, at an arbitrary admissible scaling.**  For a
symmetric positive doubled block dominating its own sharp, every skew matrix
whose corrected Schur form is below `t σ_*` bounds the reference ratio by
`1 + 6(t - 1)`. -/
theorem kappaRef_le_of_matLoewnerLE_skewCorrectedForm [NeZero d] {E : BlockMat d}
    {t : ℝ} (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E) {h0 : Mat d} (hskew : IsSkewMat h0)
    (hchain : MatLoewnerLE (skewCorrectedForm E h0) (t • schurSigmaStar E)) :
    kappaRef E ≤ 1 + 6 * (t - 1) := by
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
  -- the ordering of the two Schur blocks, and the lower bound on the scaling
  have hle : toFullBlockMat (blockSharp E) ≤ toFullBlockMat E :=
    le_of_blockMatLoewnerLE hsharpSymm hsymm hsharp
  have horder : schurSigmaStar E ≤ schurSigma E :=
    schurSigmaStar_le_schurSigma hsymm hpos hsharp
  have ht1 : 1 ≤ t :=
    one_le_of_matLoewnerLE_skewCorrectedForm hsymm hpos (matLoewnerLE_of_le horder) hchain
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  -- the skew-corrected Schur form at the given skew matrix
  set m : Mat d := schurSkew E - h0 with hmdef
  have hTsymm : (E.lowerRight)ᵀ = E.lowerRight := by
    rw [← conjTranspose_eq_transpose']; exact hTpd.isHermitian
  have hcorrEq : skewCorrectedForm E h0 = schurSigma E + mᴴ * E.lowerRight * m := by
    rw [conjTranspose_eq_transpose']
    rfl
  have hcorrPS : (mᴴ * E.lowerRight * m).PosSemidef :=
    hTpd.posSemidef.conjTranspose_mul_mul_same m
  have htLe : schurSigma E + mᴴ * E.lowerRight * m ≤ t • schurSigmaStar E := by
    refine le_of_matLoewnerLE ?_ ?_ (by rwa [hcorrEq] at hchain)
    · exact hsPd.isHermitian.add hcorrPS.isHermitian
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hstarPd.isHermitian]
      simp
  -- the two normalized quadratic bounds on the Schur skew block
  have hmT : mᴴ * E.lowerRight * m ≤ (t - 1) • schurSigmaStar E := by
    refine Matrix.le_iff.mpr ?_
    have hsum := (Matrix.le_iff.mp htLe).add (Matrix.le_iff.mp horder)
    have hrw : t • schurSigmaStar E -
          (schurSigma E + mᴴ * E.lowerRight * m) + (schurSigma E - schurSigmaStar E) =
        (t - 1) • schurSigmaStar E - mᴴ * E.lowerRight * m := by
      rw [sub_smul, one_smul]; abel
    rwa [hrw] at hsum
  have hmT' : m * E.lowerRight * mᴴ ≤ (t - 1) • schurSigmaStar E := by
    rw [schurSigmaStar] at hmT ⊢
    exact conj_transpose_le_of_conj_le hTpd (by linarith only [ht1]) hmT
  -- the symmetric part of the Schur skew block
  have hKm : schurSkew E + (schurSkew E)ᴴ = m + mᴴ := by
    have hh0 : (h0)ᴴ = -h0 := by
      rw [conjTranspose_eq_transpose']
      exact hskew
    rw [hmdef, Matrix.conjTranspose_sub, hh0]
    abel
  have hK : (schurSkew E + (schurSkew E)ᴴ)ᴴ * E.lowerRight *
      (schurSkew E + (schurSkew E)ᴴ) ≤
      (4 * (t - 1)) • schurSigmaStar E := by
    rw [hKm]
    refine Matrix.le_iff.mpr ?_
    have hbound := Matrix.le_iff.mp (conj_add_le hTpd.posSemidef m mᴴ)
    have h1 := Matrix.le_iff.mp hmT
    have h2 := Matrix.le_iff.mp hmT'
    have hsum := hbound.add (h1.add (h1.add (h2.add h2)))
    have hrw : (mᴴ * E.lowerRight * m + mᴴ * E.lowerRight * m +
            ((mᴴ)ᴴ * E.lowerRight * mᴴ + (mᴴ)ᴴ * E.lowerRight * mᴴ) -
          (m + mᴴ)ᴴ * E.lowerRight * (m + mᴴ)) +
        (((t - 1) • schurSigmaStar E - mᴴ * E.lowerRight * m) +
          (((t - 1) • schurSigmaStar E - mᴴ * E.lowerRight * m) +
            (((t - 1) • schurSigmaStar E - m * E.lowerRight * mᴴ) +
              ((t - 1) • schurSigmaStar E - m * E.lowerRight * mᴴ)))) =
        (4 * (t - 1)) • schurSigmaStar E -
          (m + mᴴ)ᴴ * E.lowerRight * (m + mᴴ) := by
      rw [Matrix.conjTranspose_conjTranspose]
      module
    rwa [hrw] at hsum
  -- the upper Schur block and the reversed comparison
  have hs : schurSigma E ≤ t • schurSigmaStar E := by
    refine le_trans (Matrix.le_iff.mpr ?_) htLe
    have hrw : schurSigma E + mᴴ * E.lowerRight * m - schurSigma E =
        mᴴ * E.lowerRight * m := by abel
    rw [hrw]
    exact hcorrPS
  have hTs : E.lowerRight ≤ t • (schurSigma E)⁻¹ := by
    have hsmulPd : (t • schurSigmaStar E).PosDef := hstarPd.smul htpos
    have hinv : (t • schurSigmaStar E)⁻¹ = t⁻¹ • E.lowerRight := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        mul_inv_cancel₀ (ne_of_gt htpos), one_smul, schurSigmaStar,
        Matrix.nonsing_inv_mul _ hdet]
    have hstep := inv_le_inv_of_le hsPd hsmulPd hs
    rw [hinv] at hstep
    have h := smul_le_smul_of_le (c := t) htpos.le hstep
    rwa [smul_smul, mul_inv_cancel₀ (ne_of_gt htpos), one_smul] at h
  -- the comparison itself
  have hsharpPd : Book.Ch02.BlockPosDef (blockSharp E) :=
    (blockPosDef_iff_posDef hsharpSymm).mpr hsharpFull
  rw [kappaRef, blockSize_eq_relSize hsymm hsharpSymm hsharpPd hEfull.posSemidef]
  refine (relSize_le_iff hEfull.posSemidef hsharpFull (by linarith only [ht1])).mpr ?_
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
    -- the sharp ordering read at the rescaled vector, second coordinate `-5 w`
    have hy' := dotProduct_mulVec_le_of_le hle
      (Sum.elim x ((-5 : ℝ) • w - (schurSkew E)ᴴ *ᵥ x))
    rw [hsharpForm, dotProduct_mulVec_schurBlock, hform,
      dotProduct_mulVec_schurBlock, hstarInv] at hy'
    have he1 : ((-5 : ℝ) • w - (schurSkew E)ᴴ *ᵥ x) - (-(schurSkew E)ᴴ) *ᵥ x
        = (-5 : ℝ) • w := by
      rw [Matrix.neg_mulVec]
      module
    have he2 : ((-5 : ℝ) • w - (schurSkew E)ᴴ *ᵥ x) - (schurSkew E) *ᵥ x
        = (-5 : ℝ) • w + (-1 : ℝ) • ((schurSkew E + (schurSkew E)ᴴ) *ᵥ x) := by
      rw [Matrix.add_mulVec]
      module
    rw [he1, he2, dotProduct_mulVec_smul_self,
      dotProduct_mulVec_smul_add_smul hTsymm] at hy'
    have hgoal : w - (schurSkew E + (schurSkew E)ᴴ) *ᵥ x
        = (1 : ℝ) • w + (-1 : ℝ) • ((schurSkew E + (schurSkew E)ᴴ) *ᵥ x) := by
      module
    rw [hgoal, dotProduct_mulVec_smul_add_smul hTsymm]
    -- the three normalized bounds
    have hA1 : x ⬝ᵥ (schurSigma E) *ᵥ x ≤ t * (x ⬝ᵥ (schurSigmaStar E) *ᵥ x) := by
      have h := dotProduct_mulVec_le_of_le hs x
      rwa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    have hA3 : ((schurSkew E + (schurSkew E)ᴴ) *ᵥ x) ⬝ᵥ E.lowerRight *ᵥ
        ((schurSkew E + (schurSkew E)ᴴ) *ᵥ x) ≤
        4 * (t - 1) * (x ⬝ᵥ (schurSigmaStar E) *ᵥ x) := by
      have h := dotProduct_mulVec_le_of_le hK x
      rw [quad_conj, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
      exact h
    have hA4 : w ⬝ᵥ E.lowerRight *ᵥ w ≤ t * (w ⬝ᵥ (schurSigma E)⁻¹ *ᵥ w) := by
      have h := dotProduct_mulVec_le_of_le hTs w
      rwa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    linarith only [hA1, hA3, hA4, hy']

/-- **The reference intermediate** `κ_𝐄 ≤ 1 + 6(Θ - 1)` of the factor-six
reference-block comparison, for a symmetric positive doubled block dominating
its own sharp. -/
theorem kappaRef_le_one_add_six_mul_refContrast_sub_one [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E) :
    kappaRef E ≤ 1 + 6 * (refContrast E - 1) := by
  obtain ⟨h, hskew, hchain⟩ := exists_isSkewMat_matLoewnerLE_refContrast_smul hsymm hpos
  exact kappaRef_le_of_matLoewnerLE_skewCorrectedForm hsymm hpos hsharp hskew hchain

/-- **The intrinsic contrast is at least one** under the sharp ordering: the
first conjunct of the printed reference row. -/
theorem one_le_refContrast [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E) :
    1 ≤ refContrast E := by
  obtain ⟨h, -, hchain⟩ := exists_isSkewMat_matLoewnerLE_refContrast_smul hsymm hpos
  exact one_le_of_matLoewnerLE_skewCorrectedForm hsymm hpos
    (matLoewnerLE_of_le (schurSigmaStar_le_schurSigma hsymm hpos hsharp)) hchain

/-- **The full printed chain** `κ_𝐄 ≤ 1 + 6(Θ - 1) ≤ 6 Π`. -/
theorem one_add_six_mul_refContrast_sub_one_le_six_mul_aspectRatio {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) :
    1 + 6 * (refContrast E - 1) ≤ 6 * aspectRatio E :=
  one_add_six_refContrast_sub_one_le (refContrast_le_aspectRatio hsymm hpos)

/-! ## The forms consumed under the coarse ellipticity assumption -/

/-- `Θ ≤ Π` at a reference block of `e.coarse.ellipticity`. -/
theorem refContrast_le_aspectRatio_of_coarseEllipticityDagger
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    refContrast E ≤ aspectRatio E :=
  refContrast_le_aspectRatio hdag.refBlock_isSymm hdag.refBlock_posDef

/-- `1 ≤ Θ` at a reference block of `e.coarse.ellipticity`. -/
theorem one_le_refContrast_of_coarseEllipticityDagger [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    1 ≤ refContrast E :=
  one_le_refContrast hdag.refBlock_isSymm hdag.refBlock_posDef
    (blockMatLoewnerLE_blockSharp_reference hdag)

/-- **The reference intermediate under the coarse ellipticity assumption.**  At a
probability law the reference block of `e.coarse.ellipticity` dominates its
own sharp, so the intermediate applies to it. -/
theorem kappaRef_le_one_add_six_mul_refContrast_sub_one_of_coarseEllipticityDagger
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    kappaRef E ≤ 1 + 6 * (refContrast E - 1) :=
  kappaRef_le_one_add_six_mul_refContrast_sub_one hdag.refBlock_isSymm
    hdag.refBlock_posDef (blockMatLoewnerLE_blockSharp_reference hdag)

/-- The printed tail `1 + 6(Θ - 1) ≤ 6 Π` at a reference block of
`e.coarse.ellipticity`. -/
theorem one_add_six_mul_refContrast_sub_one_le_six_mul_aspectRatio_of_coarseEllipticityDagger
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    1 + 6 * (refContrast E - 1) ≤ 6 * aspectRatio E :=
  one_add_six_mul_refContrast_sub_one_le_six_mul_aspectRatio hdag.refBlock_isSymm
    hdag.refBlock_posDef

end

end Initialization
end HighContrast
end HCPolySupport
