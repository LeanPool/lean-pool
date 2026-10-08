/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.EpsilonAffineLoadNormalization
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCoefficient

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.EpsilonAffineCoefficientRealization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exact coefficient realization under microscopic affine scaling

The physical scaling, real translation, skew removal, and affine square-root
gauge are assembled into one coefficient-space sample.  The scalar factors
cancel exactly in the affine conjugation.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The translated, skew-centered, microscopic coefficient sample used before
the affine pullback. -/
@[expose]
def epsilonAffinePhysicalCoeff
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (center : Vec d)
    (a : CoeffSpace d) (abar : Mat d) : CoeffSpace d :=
  ((realTranslateCoeff
      (epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center) a).subSkew
      (skewPart abar) (matTranspose_skewPart abar)).positiveScale
      (epsilonCoefficientScale epsilon)
      (epsilonCoefficientScale_pos hepsilon)

/-- The microscopic coefficient sample has the explicit translated and
rescaled representative. -/
theorem epsilonAffinePhysicalCoeff_ae
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (center : Vec d)
    (a : CoeffSpace d) (abar : Mat d) :
    (⇑(epsilonAffinePhysicalCoeff epsilon hepsilon center a abar).1 :
        CoeffField d) =ᵐ[volume]
      fun z ↦ epsilonCoefficientScale epsilon •
        (a.1 (z + epsilon⁻¹ •
          matVecMul (matSqrt (symmPart abar)) center) - skewPart abar) := by
  let z0 := epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center
  let aTrans := realTranslateCoeff z0 a
  let aSkew := aTrans.subSkew (skewPart abar) (matTranspose_skewPart abar)
  let c := epsilonCoefficientScale epsilon
  have hscale :=
    CoeffSpace.positiveScale_ae c (epsilonCoefficientScale_pos hepsilon) aSkew
  have hskew :=
    CoeffSpace.subSkew_ae aTrans (skewPart abar) (matTranspose_skewPart abar)
  have htranslate := realTranslateCoeff_ae z0 a
  filter_upwards [hscale, hskew, htranslate] with z hscalez hskewz htranslatez
  change
    (aSkew.positiveScale c (epsilonCoefficientScale_pos hepsilon)).1 z =
      c • (a.1 (z + z0) - skewPart abar)
  rw [hscalez, hskewz, htranslatez]

/-- The affine pullback of the preceding sample is exactly the translated
physical gauge coefficient.  In particular, real dilation contributes no
residual response factor. -/
theorem affineCoefficient_epsilonAffinePhysicalCoeff_ae
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (center : Vec d)
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef) :
    affineCoefficient (epsilonAffineGrid epsilon abar)
        ((Matrix.isUnit_iff_isUnit_det _).mp
          (epsilonAffineGrid_posDef hepsilon hS).isUnit)
        (⇑(epsilonAffinePhysicalCoeff epsilon hepsilon center a abar).1 :
          CoeffField d) =ᵐ[volume]
      fun x ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun y ↦ scaledCoeff epsilon a y - skewPart abar) (x + center) := by
  let M := matSqrt (symmPart abar)
  let q := epsilonAffineGrid epsilon abar
  let c := epsilonCoefficientScale epsilon
  let z0 := epsilon⁻¹ • matVecMul M center
  have hq : q.PosDef := by
    simpa only [q] using epsilonAffineGrid_posDef hepsilon hS
  let hqdet := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hM : M.PosDef := by simpa only [M] using posDef_matSqrt hS
  have hqinv : q⁻¹ = epsilon • M⁻¹ := by
    change (epsilon⁻¹ • M)⁻¹ = epsilon • M⁻¹
    rw [Response.inv_smul_posDef hM (inv_pos.mpr hepsilon)]
    congr 1
    field_simp [hepsilon.ne']
  have hcoeff := affineCoefficient_congr_ae_global q hqdet
    (epsilonAffinePhysicalCoeff_ae hepsilon center a abar)
  refine hcoeff.trans ?_
  apply Filter.Eventually.of_forall
  intro x
  have harg : matVecMul q x + z0 =
      epsilon⁻¹ • matVecMul M (x + center) := by
    ext i
    simp only [q, epsilonAffineGrid, z0, matVecMul_add, smul_matVecMul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hc : c = epsilon⁻¹ ^ 2 := rfl
  have hscale : epsilon * (epsilon * c) = 1 := by
    rw [hc]
    field_simp [hepsilon.ne']
  simp only [affineCoefficient_apply, scaledCoeff]
  rw [hqinv, harg]
  simp only [matTranspose, Matrix.transpose_smul]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, Matrix.smul_mul, smul_smul]
  have hscale' : epsilon * epsilon * epsilonCoefficientScale epsilon = 1 := by
    change epsilon * epsilon * c = 1
    calc
      epsilon * epsilon * c = epsilon * (epsilon * c) := by ring
      _ = 1 := hscale
  rw [hscale', one_smul]

end

end RowSupply
end HighContrast
end HCPolySupport
