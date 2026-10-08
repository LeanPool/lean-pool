/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseFormulas
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.SchattenSpectral

/-!
# High-contrast homogenization: Provider.Response.CenteredResponseOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Positivity of the centered response matrices

The annealed sharp order implies `SStar ≤ S`.  Consequently the two matrices
whose traces occur in the centered-response estimate are positive semidefinite,
and their sum is the normalized corrected response block.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The normalized excess of the primal Schur block. -/
@[expose]
def centeredResponseX (S SStar : Mat d) : Mat d :=
  matSqrt SStar⁻¹ * S * matSqrt SStar⁻¹ - 1

/-- The normalized symmetric-coordinate correction. -/
@[expose]
def centeredResponseY (SStar K : Mat d) : Mat d :=
  matSqrt SStar⁻¹ * (responseSymmetric K)ᴴ * SStar⁻¹ *
    responseSymmetric K * matSqrt SStar⁻¹

/-- The annealed sharp order flattened at its Schur representation. -/
theorem annealed_schur_sharp_le {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d}
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) :
    fullBlockSharp (schurBlock S SStar K) ≤ schurBlock S SStar K := by
  have hpos : BlockPosDef (annealedBlock P (U : Set (Vec d))) :=
    blockPosDef_annealedBlock hint fun a => by
      apply Sharp.blockPosDef_coarseBlock_of_volume_pos U.isDomain
      exact ENNReal.toReal_pos
        (U.isDomain.isOpen.measure_pos volume U.nonempty).ne'
        U.isDomain.volume_lt_top.ne
  have hsharp := Sharp.blockSharp_annealedBlock_le_of_nonempty
    U.isDomain U.nonempty hint
  have hfull := fullBlockSharp_le_of_blockMatLoewnerLE
    (isSymmetricBlockMat_annealedBlock P (U : Set (Vec d))) hpos hsharp
  rw [hE] at hfull
  exact hfull

/-- The lower Schur matrix is below the upper one. -/
theorem annealed_schurStar_le_schur {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) :
    SStar ≤ S :=
  schurStar_le_schur hS hStar
    (annealed_schur_sharp_le U hint hE)

/-- The symmetric response coordinate is Hermitian. -/
theorem responseSymmetric_isHermitian (K : Mat d) :
    (responseSymmetric K)ᴴ = responseSymmetric K := by
  exact conjTranspose_response_sym (K := K) (r := responseSymmetric K) rfl

/-- Removing the skew response coordinate leaves the symmetric coordinate. -/
theorem sub_responseSkew (K : Mat d) :
    K - responseSkew K = responseSymmetric K := by
  rw [responseSkew, responseSymmetric]
  module

/-- Doubling the symmetric response coordinate gives `K + Kᴴ`. -/
theorem two_smul_responseSymmetric (K : Mat d) :
    (2 : ℝ) • responseSymmetric K = K + Kᴴ := by
  rw [responseSymmetric, smul_smul]
  norm_num

/-- The corrected response block is positive definite. -/
theorem centeredResponseBlock_posDef {S SStar : Mat d}
    (hS : S.PosDef) (hStar : SStar.PosDef) (K : Mat d) :
    (centeredResponseBlock S SStar K).PosDef :=
  posDef_responseBlock hS hStar rfl

/-- The response metric is positive definite. -/
theorem centeredResponseMetric_posDef {S SStar : Mat d}
    (hS : S.PosDef) (hStar : SStar.PosDef) (K : Mat d) :
    (centeredResponseMetric S SStar K).PosDef :=
  posDef_matGeomMean (centeredResponseBlock_posDef hS hStar K) hStar

/-- The normalized Schur excess `X` is positive semidefinite. -/
theorem centeredResponseX_posSemidef {S SStar : Mat d}
    (hStar : SStar.PosDef) (horder : SStar ≤ S) :
    (centeredResponseX S SStar).PosSemidef := by
  let R : Mat d := matSqrt SStar⁻¹
  have hR : Rᴴ = R := (matSqrt_spec hStar.inv.posSemidef).1.isHermitian
  have hconj := conj_le_conj' (C := R) hR horder
  have hunit : R * SStar * R = 1 := by
    have h := matSqrt_mul_inv_mul_matSqrt hStar.inv
    simpa only [R, Matrix.nonsing_inv_nonsing_inv SStar
      (isUnit_det_of_posDef hStar)] using h
  rw [hunit] at hconj
  exact Matrix.le_iff.mp (by simpa only [centeredResponseX, R] using hconj)

/-- The symmetric-coordinate correction `Y` is positive semidefinite. -/
theorem centeredResponseY_posSemidef {SStar : Mat d}
    (hStar : SStar.PosDef) (K : Mat d) :
    (centeredResponseY SStar K).PosSemidef := by
  have hR : (matSqrt SStar⁻¹)ᴴ = matSqrt SStar⁻¹ :=
    (matSqrt_spec hStar.inv.posSemidef).1.isHermitian
  have hform : centeredResponseY SStar K =
      (responseSymmetric K * matSqrt SStar⁻¹)ᴴ * SStar⁻¹ *
        (responseSymmetric K * matSqrt SStar⁻¹) := by
    rw [centeredResponseY, Matrix.conjTranspose_mul, hR]
    noncomm_ring
  rw [hform]
  exact hStar.inv.posSemidef.conjTranspose_mul_mul_same
    (responseSymmetric K * matSqrt SStar⁻¹)

/-- The normalized corrected block is exactly `X + Y`. -/
theorem normalized_centeredResponseBlock_eq_X_add_Y
    (S SStar K : Mat d) :
    matSqrt SStar⁻¹ * centeredResponseBlock S SStar K *
          matSqrt SStar⁻¹ - 1 =
      centeredResponseX S SStar + centeredResponseY SStar K := by
  rw [centeredResponseBlock, centeredResponseX, centeredResponseY]
  noncomm_ring

end

end HCPolySupport.HighContrast.Response
