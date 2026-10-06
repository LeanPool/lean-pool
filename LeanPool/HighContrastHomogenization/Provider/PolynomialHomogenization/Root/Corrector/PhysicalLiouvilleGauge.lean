/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.LiouvilleAECongruence
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCoeffSpace

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PhysicalLiouvilleGauge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical-to-normalized Liouville transport

The physical coefficient is first recentered by its constant skew part, then
positively scaled, and finally pulled back by the normalized square root.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set Filter

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Full Liouville membership is equivalent between the physical coefficient
and any locally uniformly elliptic representative of its normalized affine
gauge. -/
theorem memLiouvilleClass_physical_normalizedPullback_iff
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef)
    {b : CoeffField d} {theta : ℝ}
    (hb : IsAELocallyUniformlyElliptic b)
    (hcoeff :
      affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ⇑(normalizedCenteredCoeff a abar hS).1 =ᵐ[volume] b)
    (v : Vec d → ℝ) (Dv : Vec d → Vec d) :
    MemLiouvilleClass (fun x ↦ a.1 x) theta v Dv ↔
      MemLiouvilleClass b theta
        (fun y ↦ v (matVecMul (Selection.normalizedRoot (symmPart abar)) y))
        (fun y ↦ matVecMul
          (matTranspose (Selection.normalizedRoot (symmPart abar)))
          (Dv (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) := by
  let L : Mat d := Selection.normalizedRoot (symmPart abar)
  let hL : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det _).mp
    (normalizedRoot_posDef_of_posDef hS).isUnit
  let k : Mat d := skewPart abar
  let centered : CoeffField d := fun x ↦ (a.1 x : Mat d) - k
  let μ : ℝ := specBound ((symmPart abar)⁻¹)
  let scaled : CoeffField d := fun x ↦ μ • centered x
  let normalized : CoeffField d := ⇑(normalizedCenteredCoeff a abar hS).1
  let affine : CoeffField d := affineCoefficient L hL normalized
  have hellCRep : IsAELocallyUniformlyElliptic
      (⇑(a.subSkew k (matTranspose_skewPart abar)).1 : CoeffField d) :=
    (a.subSkew k (matTranspose_skewPart abar)).2
  have hcenterRep :
      (⇑(a.subSkew k (matTranspose_skewPart abar)).1 : CoeffField d) =ᵐ[volume]
        centered := by
    simpa only [centered, k] using
      CoeffSpace.subSkew_ae a (skewPart abar) (matTranspose_skewPart abar)
  have hellCentered : IsAELocallyUniformlyElliptic centered :=
    hellCRep.congr hcenterRep
  have hellNormalized : IsAELocallyUniformlyElliptic normalized :=
    (normalizedCenteredCoeff a abar hS).2
  have hscaledNormalized : scaled =ᵐ[volume] normalized := by
    simpa only [scaled, centered, μ, k] using
      (normalizedCenteredCoeff_ae a abar hS).symm
  have hellScaled : IsAELocallyUniformlyElliptic scaled :=
    hellNormalized.congr hscaledNormalized.symm
  have hellAffine : IsAELocallyUniformlyElliptic affine :=
    isAELocallyUniformlyElliptic_affineCoefficient L hL hellNormalized
  have hphysicalCentered :
      MemLiouvilleClass (fun x ↦ a.1 x) theta v Dv ↔
        MemLiouvilleClass centered theta v Dv := by
    have h := memLiouvilleClass_add_constSkew_iff (theta := theta)
      hellCentered k
      (matTranspose_skewPart abar) v Dv
    simpa only [centered, k, sub_add_cancel] using h
  have hcenteredScaled :
      MemLiouvilleClass centered theta v Dv ↔
        MemLiouvilleClass scaled theta v Dv :=
    (memLiouvilleClass_smul_coefficient_iff
      (b := centered) (v := v) (Dv := Dv)
      (normalizedRootScale_pos hS)).symm
  have hscaledNormalizedClass :
      MemLiouvilleClass scaled theta v Dv ↔
        MemLiouvilleClass normalized theta v Dv :=
    memLiouvilleClass_congr_coefficient hscaledNormalized
      hellScaled hellNormalized
  have hnormalizedAffine := memLiouvilleClass_affinePullback_iff (theta := theta) hL
    hellNormalized v Dv
  have haffineB :
      MemLiouvilleClass affine theta
          (fun y ↦ v (matVecMul L y))
          (fun y ↦ matVecMul (matTranspose L) (Dv (matVecMul L y))) ↔
        MemLiouvilleClass b theta
          (fun y ↦ v (matVecMul L y))
          (fun y ↦ matVecMul (matTranspose L) (Dv (matVecMul L y))) :=
    memLiouvilleClass_congr_coefficient
      (by simpa only [affine, L, hL] using hcoeff)
      hellAffine hb
  exact hphysicalCentered.trans
    (hcenteredScaled.trans
      (hscaledNormalizedClass.trans
        (hnormalizedAffine.trans (by simpa only [affine] using haffineB))))

end

end Root
end HighContrast
end HCPolySupport
