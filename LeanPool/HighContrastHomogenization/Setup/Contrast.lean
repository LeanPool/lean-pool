/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.SpectralBound

/-!
# High-contrast homogenization: Setup.Contrast

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The intrinsic contrast in the printed form

The reference text writes the intrinsic contrast of a doubled block matrix as the
minimum over skew `h` of the conjugated norms
`|σ_*^{-1/2}(σ + (k - h)ᵗ σ_*⁻¹ (k - h)) σ_*^{-1/2}|`
(the intrinsic contrast of the reference block, and `e.Theta.m`), and the
reference constant `Λ_0` as the corresponding unconjugated minimum
(`e.reference.aspect.ratio`).  This file proves that the Loewner-scaling encodings
`blockContrast` and `bigLambdaRef` are the infima of exactly those families:
the conjugation identity turns comparison with `t σ_*` into comparison of the
conjugate with `t I`, and the threshold form of the infimum is the infimum of the
family.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

private theorem matVecMul_one'' (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem matVecMul_smul_one'' (t : ℝ) (x : Vec d) :
    matVecMul (t • (1 : Mat d)) x = t • x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq, mul_comm]

private theorem vecDot_matVecMul_smul'' (t : ℝ) (A : Mat d) (x : Vec d) :
    vecDot x (matVecMul (t • A) x) = t * vecDot x (matVecMul A x) := by
  simp only [vecDot, matVecMul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ## Infima over the skew parameter -/

theorem isSkewMat_zero : IsSkewMat (0 : Mat d) := by
  simp [IsSkewMat, matTranspose]

/-- The threshold form of an infimum over a nonnegative family indexed by the
skew matrices is the infimum of the family. -/
theorem sInf_skew_eq {f : Mat d → ℝ} (hf : ∀ h, 0 ≤ f h) :
    sInf {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧ f h ≤ t} =
      sInf (f '' {h : Mat d | IsSkewMat h}) := by
  have hBne : (f '' {h : Mat d | IsSkewMat h}).Nonempty :=
    ⟨f 0, ⟨0, isSkewMat_zero, rfl⟩⟩
  have hBA : f '' {h : Mat d | IsSkewMat h} ⊆
      {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧ f h ≤ t} := by
    rintro t ⟨h, hh, rfl⟩
    exact ⟨hf h, h, hh, le_rfl⟩
  have hAne : {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧ f h ≤ t}.Nonempty :=
    ⟨f 0, hBA ⟨0, isSkewMat_zero, rfl⟩⟩
  have hAbdd : BddBelow {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧ f h ≤ t} :=
    ⟨0, fun t ht => ht.1⟩
  have hBbdd : BddBelow (f '' {h : Mat d | IsSkewMat h}) := by
    refine ⟨0, ?_⟩
    rintro t ⟨h, -, rfl⟩
    exact hf h
  refine le_antisymm (csInf_le_csInf hAbdd hBne hBA) (le_csInf hAne ?_)
  rintro t ⟨-, h, hh, hle⟩
  exact le_trans (csInf_le hBbdd ⟨h, hh, rfl⟩) hle

/-- The skew-corrected Schur form `σ + (k - h)ᵗ σ_*⁻¹ (k - h)` of a doubled block
matrix: the matrix whose norm the reference text minimizes over skew `h`. -/
@[expose]
def skewCorrectedForm (H : BlockMat d) (h : Mat d) : Mat d :=
  schurSigma H + matTranspose (schurSkew H - h) * H.lowerRight * (schurSkew H - h)

/-- **`Λ_0` in printed form.**  The reference constant is the infimum over skew
`h` of the norms `|σ_0 + (k_0 - h)ᵗ σ_{*,0}^{-1} (k_0 - h)|`. -/
theorem bigLambdaRef_eq_sInf (E : BlockMat d) :
    bigLambdaRef E =
      sInf ((fun h => specBound (skewCorrectedForm E h)) ''
        {h : Mat d | IsSkewMat h}) := by
  rw [← sInf_skew_eq (f := fun h => specBound (skewCorrectedForm E h))
    fun h => specBound_nonneg _]
  refine congrArg sInf ?_
  ext t
  constructor
  · rintro ⟨ht, h, hh, hle⟩
    exact ⟨ht, h, hh, (specBound_le_iff ht).2 hle⟩
  · rintro ⟨ht, h, hh, hle⟩
    exact ⟨ht, h, hh, (specBound_le_iff ht).1 hle⟩

/-! ## The conjugation identity -/

/-- **The conjugation identity.**  For an invertible symmetric `R` with
`R σ R = 1`, comparison with `t σ` in the Loewner order is comparison of the
conjugate `R M R` with `t I`. -/
theorem matLoewnerLE_smul_iff_conj {σ R M : Mat d} (hR : matTranspose R = R)
    (hRR : R * σ * R = 1) (hRinv : IsUnit R.det) (t : ℝ) :
    MatLoewnerLE M (t • σ) ↔ MatLoewnerLE (R * M * R) (t • (1 : Mat d)) := by
  have hconj : ∀ x : Vec d, vecDot x (matVecMul (R * M * R) x) =
      vecDot (matVecMul R x) (matVecMul M (matVecMul R x)) := by
    intro x
    rw [← matVecMul_mul, ← matVecMul_mul, ← hR, vecDot_matVecMul_transpose, hR]
  have hnorm : ∀ x : Vec d,
      vecDot (matVecMul R x) (matVecMul σ (matVecMul R x)) = vecDot x x := by
    intro x
    rw [← vecDot_matVecMul_transpose, hR, matVecMul_mul, matVecMul_mul, hRR,
      matVecMul_one'']
  constructor
  · intro hle x
    have h := hle (matVecMul R x)
    rw [vecDot_matVecMul_smul'', hnorm x] at h
    rw [hconj x, vecDot_matVecMul_smul'', matVecMul_one'']
    exact h
  · intro hle y
    have hy : matVecMul R (matVecMul R⁻¹ y) = y := by
      rw [matVecMul_mul, Matrix.mul_nonsing_inv R hRinv, matVecMul_one'']
    have h := hle (matVecMul R⁻¹ y)
    rw [hconj (matVecMul R⁻¹ y), hy, vecDot_matVecMul_smul'', matVecMul_one''] at h
    rw [vecDot_matVecMul_smul'']
    rw [← hnorm (matVecMul R⁻¹ y), hy] at h
    exact h

/-! ## Positivity of the Schur block -/

/-- The lower-right block of a symmetric doubled block matrix is Hermitian. -/
theorem isHermitian_lowerRight {H : BlockMat d} (hsymm : IsSymmetricBlockMat H) :
    H.lowerRight.IsHermitian := by
  ext i j
  exact hsymm (Sum.inr j) (Sum.inr i)

/-- The lower-right block of a symmetric positive definite doubled block matrix
is positive semidefinite. -/
theorem posSemidef_lowerRight {H : BlockMat d} (hsymm : IsSymmetricBlockMat H)
    (hpos : Book.Ch02.BlockPosDef H) : H.lowerRight.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_lowerRight hsymm)
    fun x => ?_
  show (0 : ℝ) ≤ vecDot x (matVecMul H.lowerRight x)
  by_cases hx : x = 0
  · subst hx
    simp [vecDot, matVecMul]
  · refine le_of_lt ?_
    rw [← blockVecDot_inr]
    exact hpos ((0 : Vec d), x) fun hc => hx (congrArg Prod.snd hc)

/-- The lower-right block of a positive definite doubled block matrix is
invertible. -/
theorem isUnit_det_lowerRight {H : BlockMat d}
    (hpos : Book.Ch02.BlockPosDef H) : IsUnit H.lowerRight.det := by
  refine Ne.isUnit ?_
  intro h0
  obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hq := hpos ((0 : Vec d), v) fun hc => hv (congrArg Prod.snd hc)
  rw [blockVecDot_inr] at hq
  have hzero : vecDot v (matVecMul H.lowerRight v) = 0 := by
    have hm : matVecMul H.lowerRight v = 0 := hmv
    rw [hm]
    simp [vecDot]
  rw [hzero] at hq
  exact lt_irrefl 0 hq

/-- The conjugating matrix is the inverse square root of the Schur block: the
lower-right block is `σ_*⁻¹`, so `matSqrt H.lowerRight` is `σ_*^{-1/2}`. -/
theorem schurSigmaStar_inv (H : BlockMat d) (hdet : IsUnit H.lowerRight.det) :
    (schurSigmaStar H)⁻¹ = H.lowerRight := by
  rw [schurSigmaStar, Matrix.nonsing_inv_nonsing_inv _ hdet]

/-- **The intrinsic contrast in printed form.**  On a symmetric positive definite
doubled block matrix the Loewner-scaling infimum is the infimum over skew `h` of
the conjugated norms
`|σ_*^{-1/2} (σ + (k - h)ᵗ σ_*⁻¹ (k - h)) σ_*^{-1/2}|`;
the conjugating matrix is the positive semidefinite square root of
`σ_*⁻¹ = H.lowerRight`. -/
theorem blockContrast_eq_sInf_conj {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : Book.Ch02.BlockPosDef H) :
    blockContrast H =
      sInf ((fun h => specBound (matSqrt H.lowerRight * skewCorrectedForm H h *
        matSqrt H.lowerRight)) '' {h : Mat d | IsSkewMat h}) := by
  have hdet : IsUnit H.lowerRight.det := isUnit_det_lowerRight hpos
  obtain ⟨hRpsd, hRR⟩ := matSqrt_spec (posSemidef_lowerRight hsymm hpos)
  set R : Mat d := matSqrt H.lowerRight with hRdef
  have hRsymm : matTranspose R = R := by
    have := hRpsd.isHermitian
    ext i j
    simpa [matTranspose, Matrix.IsHermitian, Matrix.conjTranspose_apply] using
      congrArg (fun M : Mat d => M i j) this
  have hRdet : IsUnit R.det := by
    refine isUnit_of_mul_isUnit_left (y := R.det) ?_
    rw [← Matrix.det_mul, hRR]
    exact hdet
  have hRRinv : R * schurSigmaStar H * R = 1 := by
    rw [schurSigmaStar, ← hRR, Matrix.mul_inv_rev]
    calc R * (R⁻¹ * R⁻¹) * R = (R * R⁻¹) * (R⁻¹ * R) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.mul_nonsing_inv R hRdet, Matrix.nonsing_inv_mul R hRdet, one_mul]
  rw [← sInf_skew_eq
    (f := fun h => specBound (R * skewCorrectedForm H h * R))
    fun h => specBound_nonneg _]
  refine congrArg sInf ?_
  ext t
  constructor
  · rintro ⟨ht, h, hh, hle⟩
    exact ⟨ht, h, hh, (specBound_le_iff ht).2
      ((matLoewnerLE_smul_iff_conj hRsymm hRRinv hRdet t).1 hle)⟩
  · rintro ⟨ht, h, hh, hle⟩
    exact ⟨ht, h, hh, (matLoewnerLE_smul_iff_conj hRsymm hRRinv hRdet t).2
      ((specBound_le_iff ht).1 hle)⟩

end

end HighContrast
end HCPolySupport
