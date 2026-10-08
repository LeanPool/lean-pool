/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioMonotone
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio
public import LeanPool.HighContrastHomogenization.Provider.Quenched.BlockScaleGeometry
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedBlockPositivity

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.HomogenizedEccentricityBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The eccentricity of the homogenized matrix is polynomial in the reference data

The homogenized coefficient matrix is pinned by a two-sided annealed sandwich,
and the coarse-ellipticity assumption puts every annealed block below a scalar
multiple of the reference block.  The doubled block of the homogenized matrix is
therefore below a scalar multiple of the reference block, and the reference
aspect ratio is monotone for that order and homogeneous of degree two under the
dilation.

The doubled block of a coefficient matrix has the matrix's symmetric part as its
Schur block and the inverse of that symmetric part as its lower-right block, so
its aspect ratio dominates the square of the witness eccentricity of the
symmetric part.  Composing gives a bound on the eccentricity by a fixed power of
`2 + Π K`, the same polynomial length datum the statement already carries.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The Schur data of a constant doubled block -/

/-- The Schur skew block of the doubled block of a coefficient matrix is the
matrix's skew part. -/
theorem schurSkew_constantBlockMatrix {a0 : Mat d} (hS : (symmPart a0).PosDef) :
    schurSkew (Book.Ch02.constantBlockMatrix a0) = skewPart a0 := by
  have hdet : IsUnit (symmPart a0).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  have hinv : ((symmPart a0)⁻¹)⁻¹ = symmPart a0 :=
    Matrix.nonsing_inv_nonsing_inv _ hdet
  have hmul : symmPart a0 * (symmPart a0)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  change -(((symmPart a0)⁻¹)⁻¹ * -((symmPart a0)⁻¹ * skewPart a0)) = skewPart a0
  rw [hinv, Matrix.mul_neg, neg_neg, ← Matrix.mul_assoc, hmul, Matrix.one_mul]

/-- The Schur block of the doubled block of a coefficient matrix is the matrix's
symmetric part. -/
theorem schurSigma_constantBlockMatrix {a0 : Mat d} (hS : (symmPart a0).PosDef) :
    schurSigma (Book.Ch02.constantBlockMatrix a0) = symmPart a0 := by
  rw [schurSigma, schurSkew_constantBlockMatrix hS]
  change symmPart a0 +
      matTranspose (skewPart a0) * (symmPart a0)⁻¹ * skewPart a0 -
        matTranspose (skewPart a0) * (symmPart a0)⁻¹ * skewPart a0 =
    symmPart a0
  abel

/-- The lower-right block of the doubled block of a coefficient matrix is the
inverse of the matrix's symmetric part. -/
theorem lowerRight_constantBlockMatrix (a0 : Mat d) :
    (Book.Ch02.constantBlockMatrix a0).lowerRight = (symmPart a0)⁻¹ := rfl

/-! ## The eccentricity against the aspect ratio of the doubled block -/

/-- **The eccentricity is controlled by the aspect ratio of the doubled block.**
The Schur block contributes the spectral bound of the symmetric part, which is
below the reference constant `Λ_0` of the doubled block, and the lower-right
block contributes the spectral bound of the inverse exactly. -/
theorem witnessEccentricity_sq_le_aspectRatio_constantBlockMatrix
    {a0 : Mat d} (hS : (symmPart a0).PosDef) :
    witnessEccentricity (symmPart a0) ^ 2 ≤
      aspectRatio (Book.Ch02.constantBlockMatrix a0) := by
  have hApos : Book.Ch02.BlockPosDef (Book.Ch02.constantBlockMatrix a0) :=
    blockPosDef_constantBlockMatrix_of_posDef_symmPart hS
  have hsigma : specBound (symmPart a0) ≤
      bigLambdaRef (Book.Ch02.constantBlockMatrix a0) := by
    refine specBound_le (bigLambdaRef_nonneg _) ?_
    rw [← schurSigma_constantBlockMatrix hS]
    exact matLoewnerLE_schurSigma_bigLambdaRef_smul_one hApos
  have hprod : (0 : ℝ) ≤ specBound (symmPart a0) * specBound (symmPart a0)⁻¹ :=
    mul_nonneg (specBound_nonneg _) (specBound_nonneg _)
  rw [witnessEccentricity, Real.sq_sqrt hprod,
    aspectRatio_eq_bigLambdaRef_mul_specBound, lowerRight_constantBlockMatrix]
  exact mul_le_mul_of_nonneg_right hsigma (specBound_nonneg _)

/-! ## The arithmetic of the polynomial length -/

/-- The closing arithmetic: a bound of the shape `c ≤ 1 + 6K²` on the dilation
constant and `1 ≤ Π` on the aspect ratio give the fifth power of the printed
polynomial length datum. -/
theorem mul_le_pow_two_add_mul {c Pi K : ℝ} (hPi : 1 ≤ Pi) (hK : 1 < K)
    (hc : c ≤ 1 + 6 * K ^ 2) :
    c * Pi ≤ (2 + Pi * K) ^ (5 : ℕ) := by
  have hK0 : (0 : ℝ) < K := lt_trans zero_lt_one hK
  have hPi0 : (0 : ℝ) ≤ Pi := le_trans zero_le_one hPi
  have hPiK : 1 ≤ Pi * K := one_le_mul_of_one_le_of_one_le hPi hK.le
  have hB3 : (3 : ℝ) ≤ 2 + Pi * K := by linarith only [hPiK]
  have hB0 : (0 : ℝ) ≤ 2 + Pi * K := by linarith only [hB3]
  have hKPiK : K ≤ Pi * K := le_mul_of_one_le_left hK0.le hPi
  have hKB : K ≤ 2 + Pi * K := by linarith only [hKPiK]
  have hPiPiK : Pi ≤ Pi * K := le_mul_of_one_le_right hPi0 hK.le
  have hPiB : Pi ≤ 2 + Pi * K := by linarith only [hPiPiK]
  have hKsq : K ^ 2 ≤ (2 + Pi * K) ^ 2 := pow_le_pow_left₀ hK0.le hKB 2
  have hB2 : (9 : ℝ) ≤ (2 + Pi * K) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hB3 2
    linarith only [this]
  have hc7 : c ≤ 7 * (2 + Pi * K) ^ 2 := by
    linarith only [hc, hKsq, hB2]
  have hcube : (0 : ℝ) ≤ (2 + Pi * K) ^ 3 := by positivity
  have hstep : c * Pi ≤ (7 * (2 + Pi * K) ^ 2) * (2 + Pi * K) :=
    mul_le_mul hc7 hPiB hPi0 (by linarith only [hB2])
  have hfinal : (7 * (2 + Pi * K) ^ 2) * (2 + Pi * K) ≤ (2 + Pi * K) ^ (5 : ℕ) := by
    have hgap : 7 * (2 + Pi * K) ^ 3 ≤ (2 + Pi * K) ^ 2 * (2 + Pi * K) ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith only [hB2]) hcube
    calc (7 * (2 + Pi * K) ^ 2) * (2 + Pi * K) = 7 * (2 + Pi * K) ^ 3 := by ring
      _ ≤ (2 + Pi * K) ^ 2 * (2 + Pi * K) ^ 3 := hgap
      _ = (2 + Pi * K) ^ (5 : ℕ) := by ring
  exact hstep.trans hfinal

/-! ## The law-level bound -/

/-- **The homogenized eccentricity is polynomial in the reference data.**  The
witness eccentricity of the symmetric part of the homogenized matrix is bounded
by the fifth power of `2 + Π K`, with an exponent independent of the law, the
reference block, the gauge and the source scale.

The hypotheses are exactly the data the root assembly holds where the
homogenized matrix is produced: the coarse-ellipticity assumption, the symmetry
and the lower half of the annealed sandwich pinning the limiting block, and the
identification of that block as the doubled block of the homogenized matrix. -/
theorem witnessEccentricity_symmPart_le_rpow_aspectRatio [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    {Abar : BlockMat d} {abar : Mat d}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    (hS : (symmPart abar).PosDef)
    (hAbarSymm : IsSymmetricBlockMat Abar)
    (hlower : ∀ m : ℕ,
      BlockMatLoewnerLE Abar (annealedBlock P (centeredCube d (m : ℤ))))
    (hAbarEq : Book.Ch02.constantBlockMatrix abar = Abar) :
    witnessEccentricity (symmPart abar) ≤
      (2 + aspectRatio E * K) ^ (5 : ℝ) := by
  classical
  have hg : g ∈ Set.Ico (0 : ℝ) 1 := hdag.g_mem
  have hK : 1 < K := hdag.one_lt_growthWitness
  have hPi : 1 ≤ aspectRatio E := one_le_aspectRatio_of_coarseEllipticityDagger hdag
  set cA : ℝ := (1 + 6 * K ^ 2 * (3 : ℝ) ^ (-(0 : ℤ))) ^ g with hcAdef
  have hbase : (1 : ℝ) ≤ 1 + 6 * K ^ 2 * (3 : ℝ) ^ (-(0 : ℤ)) := by
    have : (0 : ℝ) ≤ 6 * K ^ 2 * (3 : ℝ) ^ (-(0 : ℤ)) := by positivity
    linarith only [this]
  have hcApos : (0 : ℝ) < cA := by
    rw [hcAdef]
    exact Real.rpow_pos_of_pos (by linarith only [hbase]) g
  have hcAle : cA ≤ 1 + 6 * K ^ 2 := by
    have hstep : cA ≤ (1 + 6 * K ^ 2 * (3 : ℝ) ^ (-(0 : ℤ))) ^ (1 : ℝ) := by
      rw [hcAdef]
      exact Real.rpow_le_rpow_of_exponent_le hbase hg.2.le
    rw [Real.rpow_one] at hstep
    have hone : (3 : ℝ) ^ (-(0 : ℤ)) = 1 := by norm_num
    rw [hone, mul_one] at hstep
    exact hstep
  -- the doubled block of the homogenized matrix, below a dilation of the reference
  have hApos : Book.Ch02.BlockPosDef (Book.Ch02.constantBlockMatrix abar) :=
    blockPosDef_constantBlockMatrix_of_posDef_symmPart hS
  have hAsymm : IsSymmetricBlockMat (Book.Ch02.constantBlockMatrix abar) := by
    rw [hAbarEq]; exact hAbarSymm
  have hscaledSymm : IsSymmetricBlockMat (blockScale cA E) :=
    isSymmetricBlockMat_blockScale cA hdag.refBlock_isSymm
  have hscaledPos : Book.Ch02.BlockPosDef (blockScale cA E) := by
    intro X hX
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
    exact mul_pos hcApos (hdag.refBlock_posDef X hX)
  have hlow : BlockMatLoewnerLE (Book.Ch02.constantBlockMatrix abar)
      (annealedBlock P (centeredCube d (0 : ℤ))) := by
    rw [hAbarEq]
    simpa only [Nat.cast_zero] using hlower 0
  have hup : BlockMatLoewnerLE (annealedBlock P (centeredCube d (0 : ℤ)))
      (blockScale cA E) := by
    rw [hcAdef]
    exact Entry.annealedBlock_centeredCube_le_blockScale hdag (0 : ℤ)
  have haspect : aspectRatio (Book.Ch02.constantBlockMatrix abar) ≤
      cA ^ 2 * aspectRatio E := by
    have hmono := aspectRatio_mono hAsymm hApos hscaledSymm hscaledPos
      (hlow.trans hup)
    rwa [Quenched.aspectRatio_blockScale hcApos E] at hmono
  -- the eccentricity below the aspect ratio, then the arithmetic
  have hsq : witnessEccentricity (symmPart abar) ^ 2 ≤ cA ^ 2 * aspectRatio E :=
    (witnessEccentricity_sq_le_aspectRatio_constantBlockMatrix hS).trans haspect
  have hPiPi : cA ^ 2 * aspectRatio E ≤ (cA * aspectRatio E) ^ 2 := by
    have hcA2 : (0 : ℝ) ≤ cA ^ 2 := by positivity
    have hstep : aspectRatio E ≤ aspectRatio E ^ 2 := by
      have := mul_le_mul_of_nonneg_left hPi (le_trans zero_le_one hPi)
      calc aspectRatio E = aspectRatio E * 1 := (mul_one _).symm
        _ ≤ aspectRatio E * aspectRatio E := this
        _ = aspectRatio E ^ 2 := by ring
    calc cA ^ 2 * aspectRatio E ≤ cA ^ 2 * aspectRatio E ^ 2 :=
          mul_le_mul_of_nonneg_left hstep hcA2
      _ = (cA * aspectRatio E) ^ 2 := by ring
  have heccNonneg : (0 : ℝ) ≤ witnessEccentricity (symmPart abar) :=
    Real.sqrt_nonneg _
  have hprodNonneg : (0 : ℝ) ≤ cA * aspectRatio E :=
    mul_nonneg hcApos.le (le_trans zero_le_one hPi)
  have hle : witnessEccentricity (symmPart abar) ≤ cA * aspectRatio E := by
    have hroot := Real.sqrt_le_sqrt (hsq.trans hPiPi)
    rwa [Real.sqrt_sq heccNonneg, Real.sqrt_sq hprodNonneg] at hroot
  have harith : cA * aspectRatio E ≤ (2 + aspectRatio E * K) ^ (5 : ℕ) :=
    mul_le_pow_two_add_mul hPi hK hcAle
  have hcast : (2 + aspectRatio E * K) ^ (5 : ℝ) =
      (2 + aspectRatio E * K) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast (2 + aspectRatio E * K) 5]
    norm_num
  rw [hcast]
  exact hle.trans harith

end

end RowSupply
end HighContrast
end HCPolySupport
