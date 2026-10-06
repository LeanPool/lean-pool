/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.RealTranslationDoubledResponse
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedResponseCell
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationLoads

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.EpsilonAffineLoadNormalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Load normalization for the microscopic affine gauge

Microscopic dilation is absorbed into the affine grid and the positive scalar
coefficient normalization.  The resulting transformed loads are exactly the
usual normalized-reference loads.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The affine grid after passing from physical to microscopic coordinates. -/
@[expose]
def epsilonAffineGrid (epsilon : ℝ) (abar : Mat d) : Mat d :=
  epsilon⁻¹ • matSqrt (symmPart abar)

/-- The coefficient multiplier paired with `epsilonAffineGrid`. -/
@[expose]
def epsilonCoefficientScale (epsilon : ℝ) : ℝ := epsilon⁻¹ ^ 2

theorem epsilonAffineGrid_posDef {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {abar : Mat d} (hS : (symmPart abar).PosDef) :
    (epsilonAffineGrid epsilon abar).PosDef := by
  exact (posDef_matSqrt hS).smul (inv_pos.mpr hepsilon)

theorem epsilonCoefficientScale_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < epsilonCoefficientScale epsilon := by
  exact sq_pos_of_pos (inv_pos.mpr hepsilon)

theorem sqrt_epsilonCoefficientScale {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Real.sqrt (epsilonCoefficientScale epsilon) = epsilon⁻¹ := by
  rw [epsilonCoefficientScale, Real.sqrt_sq_eq_abs,
    abs_of_pos (inv_pos.mpr hepsilon)]

/-- Primal loads transformed by microscopic scalar normalization and the
microscopic affine grid coincide with the normalized-reference primal load. -/
theorem affine_scalar_skew_primalLoad_epsilon_eq_normalizedReference
    [NeZero d] {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (abar : Mat d) (hS : (symmPart abar).PosDef) (P : BlockVec d) :
    affineReferencePrimalLoad (epsilonAffineGrid epsilon abar)
        (scalarNormalizedPrimalLoad
          (Real.sqrt (epsilonCoefficientScale epsilon))
          (skewCenteredPrimalLoad (skewPart abar) P)) =
      normalizedReferencePrimalLoad abar P := by
  rcases P with ⟨p, r⟩
  let M := matSqrt (symmPart abar)
  let alpha := Real.sqrt (specBound (symmPart abar)⁻¹)
  have heinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hM : M.PosDef := by simpa only [M] using posDef_matSqrt hS
  have hMinv : (epsilon⁻¹ • M)⁻¹ = epsilon • M⁻¹ := by
    rw [Response.inv_smul_posDef hM heinv]
    congr 1
    field_simp [hepsilon.ne']
  have hroot : Selection.normalizedRoot (symmPart abar) = alpha • M := by
    rfl
  have halpha : 0 < alpha := by
    exact Real.sqrt_pos.mpr (normalizedRootScale_pos hS)
  rw [sqrt_epsilonCoefficientScale hepsilon]
  simp only [affineReferencePrimalLoad, scalarNormalizedPrimalLoad,
    skewCenteredPrimalLoad, epsilonAffineGrid]
  rw [inv_inv]
  change
    (matVecMul (matTranspose (epsilon⁻¹ • matSqrt (symmPart abar))) (epsilon • p),
      matVecMul (epsilon⁻¹ • matSqrt (symmPart abar))⁻¹
        (epsilon⁻¹ • (r - matVecMul (skewPart abar) p))) = _
  change _ =
    (matVecMul (matTranspose (Selection.normalizedRoot (symmPart abar)))
        (alpha⁻¹ • p),
      matVecMul (Selection.normalizedRoot (symmPart abar))⁻¹
        (alpha • (r - matVecMul (skewPart abar) p)))
  rw [hroot, hMinv, Response.inv_smul_posDef hM halpha]
  apply Prod.ext
  · ext i
    dsimp only [M]
    simp only [matTranspose, Matrix.transpose_smul, matVecMul_smul,
      smul_matVecMul, Pi.smul_apply, smul_eq_mul]
    field_simp [hepsilon.ne', halpha.ne']
  · ext i
    simp only [matVecMul_smul, smul_matVecMul, Pi.smul_apply, smul_eq_mul]
    field_simp [hepsilon.ne', halpha.ne']

/-- The analogous identity for dual loads. -/
theorem affine_scalar_skew_dualLoad_epsilon_eq_normalizedReference
    [NeZero d] {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (abar : Mat d) (hS : (symmPart abar).PosDef) (Q : BlockVec d) :
    affineReferenceDualLoad (epsilonAffineGrid epsilon abar)
        (scalarNormalizedDualLoad
          (Real.sqrt (epsilonCoefficientScale epsilon))
          (skewCenteredDualLoad (skewPart abar) Q)) =
      normalizedReferenceDualLoad abar Q := by
  rcases Q with ⟨rStar, pStar⟩
  let M := matSqrt (symmPart abar)
  let alpha := Real.sqrt (specBound (symmPart abar)⁻¹)
  have heinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hM : M.PosDef := by simpa only [M] using posDef_matSqrt hS
  have hMinv : (epsilon⁻¹ • M)⁻¹ = epsilon • M⁻¹ := by
    rw [Response.inv_smul_posDef hM heinv]
    congr 1
    field_simp [hepsilon.ne']
  have hroot : Selection.normalizedRoot (symmPart abar) = alpha • M := by
    rfl
  have halpha : 0 < alpha := by
    exact Real.sqrt_pos.mpr (normalizedRootScale_pos hS)
  rw [sqrt_epsilonCoefficientScale hepsilon]
  simp only [affineReferenceDualLoad, scalarNormalizedDualLoad,
    skewCenteredDualLoad, epsilonAffineGrid]
  rw [inv_inv]
  change
    (matVecMul (epsilon⁻¹ • matSqrt (symmPart abar))⁻¹
        (epsilon⁻¹ • (rStar - matVecMul (skewPart abar) pStar)),
      matVecMul (matTranspose (epsilon⁻¹ • matSqrt (symmPart abar)))
        (epsilon • pStar)) = _
  change _ =
    (matVecMul (Selection.normalizedRoot (symmPart abar))⁻¹
        (alpha • (rStar - matVecMul (skewPart abar) pStar)),
      matVecMul (matTranspose (Selection.normalizedRoot (symmPart abar)))
        (alpha⁻¹ • pStar))
  rw [hroot, hMinv, Response.inv_smul_posDef hM halpha]
  apply Prod.ext
  · ext i
    simp only [matVecMul_smul, smul_matVecMul, Pi.smul_apply, smul_eq_mul]
    field_simp [hepsilon.ne', halpha.ne']
  · ext i
    dsimp only [M]
    simp only [matTranspose, Matrix.transpose_smul, matVecMul_smul,
      smul_matVecMul, Pi.smul_apply, smul_eq_mul]
    field_simp [hepsilon.ne', halpha.ne']

end

end RowSupply
end HighContrast
end HCPolySupport
