/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.RowRetainingGoodScaleInterface
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicMidpointNormalizedReferencePowerTail

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.FormulaicRowLevelWindowTailComposition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Row-level order conversion in the epsilon frame

The stochastic row is transported first.  The midpoint-order converter is
then applied to that transported row, before any all-depth observation
aggregation.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- The row-retaining root interface gives a response-window reference tail
in the triadically scaled frame. -/
theorem RowRetainingPrintOrderGoodScale.exists_formulaicScaledResponseWindowTail
    [NeZero d] {g c kappaRate : ℝ} {abar : Mat d}
    {a : CoeffSpace d} {x epsilon : ℝ}
    (h : RowRetainingPrintOrderGoodScale d g c kappaRate abar a x)
    (hS : (symmPart abar).PosDef)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hkappa : 0 < kappaRate)
    (hx : 1 ≤ x) (hepsilon : 0 < epsilon) (hscale : x ≤ epsilon⁻¹) :
    ∃ (N G : ℕ) (lambda deltaScaled : ℝ)
        (aScaled : CoeffSpace d) (aRef : Book.Ch03.CoeffFamily d) (L : ℕ),
      lambda = epsilon * (3 : ℝ) ^ N ∧
      lambda ∈ Set.Icc (1 : ℝ) 3 ∧
      aScaled = Quenched.physicalScaleCoefficient N a ∧
      deltaScaled = triadicallyScaledRowAmplitude h.delta
        (h.activationScale a) N (2 * kappaRate) ∧
      witnessEccentricity (symmPart abar) * Real.sqrt d ≤
          (3 : ℝ) ^ (G : ℤ) ∧
      (3 : ℝ) ^ (G : ℤ) ≤
          1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d) ∧
      L = Certificate.formulaicNormalizedReferenceTailShift d
          (responseWindowOrder g) (Certificate.printRowOrder g)
            (2 * kappaRate) G ∧
      (L : ℝ) < max 0 (Real.logb 3
          (Certificate.shiftedTailAbsorptionPrefactor d
            (responseWindowOrder g) (Certificate.printRowOrder g) G) /
              (2 * kappaRate)) + 1 ∧
      (∀ Q : TriadicCube d,
        (aRef.coeffOn Q).toCoeffField =
          affineCoefficient (Selection.normalizedRoot (symmPart abar))
            ((Matrix.isUnit_iff_isUnit_det _).mp
              (normalizedRoot_posDef_of_posDef hS).isUnit)
            ⇑(normalizedCenteredCoeff aScaled abar hS).1) ∧
      ScalarIdentityPowerTail aRef (responseWindowOrder g)
        (Real.sqrt deltaScaled) kappaRate ((3 : ℝ) ^ (L : ℤ)) := by
  obtain ⟨N, hXN, _hInvN, _hNInv, hlambdaOne, hlambdaThree⟩ :=
    exists_triadicScaleBracket_of_commonScale_le_inv hepsilon hx hscale
  let lambda : ℝ := epsilon * (3 : ℝ) ^ N
  let aScaled : CoeffSpace d := Quenched.physicalScaleCoefficient N a
  let deltaScaled : ℝ := triadicallyScaledRowAmplitude h.delta
    (h.activationScale a) N (2 * kappaRate)
  have hrowScaled : Quenched.HasAllLaterPhysicalBlockRow
      (Certificate.printRowOrder g) (2 * kappaRate) deltaScaled
        (Book.Ch02.constantBlockMatrix abar) (fun _ ↦ 1) (fun _ ↦ 1)
          aScaled := by
    exact hasAllLaterPhysicalBlockRow_physicalScaleCoeff
      (Certificate.printRowOrder g) (2 * kappaRate) h.delta
        (Book.Ch02.constantBlockMatrix abar) h.sourceScale h.activationScale
          a N h.row h.activation_one h.source_le_activation
            (h.activation_le_common.trans hXN)
  have hdeltaScaled : 0 ≤ deltaScaled :=
    mul_nonneg h.delta_nonneg
      (Real.rpow_nonneg
        (div_nonneg (zero_le_one.trans h.activation_one) (by positivity)) _)
  obtain ⟨G, aRef, L, hG, hGupper, hLeq, hLupper, haRef, htail⟩ :=
    exists_midpointNormalizedReferencePowerTail_with_formulaicShift
      aScaled abar hS (fun _ ↦ 1) (fun _ ↦ 1) hg (by positivity)
        hdeltaScaled hrowScaled (by norm_num) (by norm_num)
  refine ⟨N, G, lambda, deltaScaled, aScaled, aRef, L, rfl,
    ⟨hlambdaOne, hlambdaThree⟩, rfl, rfl, hG, hGupper, hLeq,
      hLupper, haRef, ?_⟩
  have hceil : Quenched.triadicCeilingIndex (1 : ℝ) = 0 := by
    simp [Quenched.triadicCeilingIndex]
  have hrate : 2 * kappaRate / 2 = kappaRate := by ring
  simpa only [midpointResponseOrder, responseWindowOrder, hceil, zero_add,
    Nat.cast_ofNat, Nat.cast_add, Nat.cast_zero,
    hrate] using htail

end

end RowSupply
end HighContrast
end HCPolySupport
