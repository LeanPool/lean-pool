/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedOuterSpatialResponsePowerTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderEffectiveScale
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedResponseScale

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedResponseRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded response rows at the printed-order common scale

The stochastic certificate and every rounded weak-error row use the order
selected after `g`.  The common scale contains the exact boundary-layer loss
for that order.
-/

namespace HCPolySupport
namespace HighContrast
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The common quantitative scale with the printed-order response loss. -/
@[expose]
noncomputable def printOrderCommonQuantitativeAffineScale
    (d : ℕ) (g sourceAmplitude target kappa : ℝ)
    (abar : Mat d) (X : CoeffSpace d → ℝ) (a : CoeffSpace d) : ℝ :=
  commonQuantitativeAffineScale sourceAmplitude target kappa
    (printOrderRoundedResponseAffineConstant d g)
    (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
    kappa X a

/-- Targeting preserves the printed reference family on every adapted cell. -/
theorem
    PrintOrderQuantitativeNormalizedReferenceCertificate.exists_targetedRoundedReferenceCoeffFamily
    [NeZero d] {a : CoeffSpace d} {abar : Mat d}
    {g sourceAmplitude target kappa : ℝ} {X : CoeffSpace d → ℝ}
    (h : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g sourceAmplitude kappa (X a) a)
    (hTarget : 0 < target) (t : ℤ) :
    ∃ (hS : (symmPart abar).PosDef) (aRef : Book.Ch03.CoeffFamily d),
      0 < printCertificateOrder g ∧
      printCertificateOrder g < 1 / 2 ∧
      0 ≤ target ∧ 0 < kappa ∧ 1 ≤ X a ∧
      (∀ R : TriadicCube d,
        (aRef.coeffOn R).toCoeffField =
          affineCoefficient (Selection.normalizedRoot (symmPart abar))
            ((Matrix.isUnit_iff_isUnit_det _).mp
              (normalizedRoot_posDef_of_posDef hS).isUnit)
            ((normalizedCenteredCoeff a abar hS).coeffOn
              (Response.adaptedDomain
                (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField) ∧
      ScalarIdentityPowerTail aRef (printCertificateOrder g) target kappa
        (targetedQuantitativeEffectiveScale
          sourceAmplitude target kappa X a) := by
  have hTargeted := h.targetedEffectiveScale hTarget
  obtain ⟨hS, aRef, hs, hsHalf, hTargetNonneg, hKappa, _, haRef, hTail⟩ :=
    hTargeted
  obtain ⟨_, _, _, _, _, _, hX, _, _⟩ := h
  refine ⟨hS, aRef, hs, hsHalf, hTargetNonneg, hKappa, hX, ?_, hTail⟩
  intro R
  simpa only [CoeffSpace.coeffOn_toCoeffField] using haRef R

private theorem physical_ratio_rpow_le_geometric_gap
    {x kappa : ℝ} {n k : ℤ} (hx : 0 < x)
    (hxn : x ≤ (3 : ℝ) ^ n) (hkappa : 0 < kappa) :
    (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
      (3 : ℝ) ^ (-kappa * ((k : ℝ) - (n : ℝ))) := by
  have hkpow : 0 < (3 : ℝ) ^ k := by positivity
  have hratio : 0 < ((3 : ℝ) ^ k) / x := div_pos hkpow hx
  have hgap : 0 < (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) := by positivity
  have hbase : (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) ≤ ((3 : ℝ) ^ k) / x := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3),
      Real.rpow_intCast, Real.rpow_intCast]
    exact div_le_div_of_nonneg_left hkpow.le hx hxn
  calc
    (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
        ((3 : ℝ) ^ ((k : ℝ) - (n : ℝ))) ^ (-kappa) :=
      (Real.rpow_le_rpow_iff_of_neg hratio hgap
        (neg_neg_of_pos hkappa)).2 hbase
    _ = (3 : ℝ) ^ (((k : ℝ) - (n : ℝ)) * (-kappa)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
    _ = (3 : ℝ) ^ (-kappa * ((k : ℝ) - (n : ℝ))) := by
      congr 1
      ring

end

end HighContrast
end HCPolySupport
