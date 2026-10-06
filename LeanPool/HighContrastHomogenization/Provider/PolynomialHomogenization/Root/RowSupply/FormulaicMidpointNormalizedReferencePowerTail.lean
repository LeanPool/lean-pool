/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.MidpointResponseOrder
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicShiftedNormalizedReferencePowerTail

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.FormulaicMidpointNormalizedReferencePowerTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Formulaically shifted midpoint normalized-reference tails

The midpoint specialization retains the exact old converter interface and
also exports the enclosure generation, the formulaic shift, and its strict
deterministic upper bound.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book.Ch02 Certificate

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The midpoint converter with the enclosure and formulaic shift data kept
in its conclusion. -/
theorem exists_midpointNormalizedReferencePowerTail_with_formulaicShift
    [NeZero d] (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) {g kappa delta : ℝ}
    (S X : CoeffSpace d → ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hkappa : 0 < kappa) (hdelta : 0 ≤ delta)
    (hrow : Quenched.HasAllLaterPhysicalBlockRow
      (printRowOrder g) kappa delta
        (Book.Ch02.constantBlockMatrix abar) S X a)
    (hXone : 1 ≤ X a) (hburn : S a ≤ X a) :
    ∃ G : ℕ, ∃ aRef : Book.Ch03.CoeffFamily d, ∃ L : ℕ,
      witnessEccentricity (symmPart abar) * Real.sqrt d ≤
          (3 : ℝ) ^ (G : ℤ) ∧
      (3 : ℝ) ^ (G : ℤ) ≤
          1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d) ∧
      L = formulaicNormalizedReferenceTailShift d
          (midpointResponseOrder g) (printRowOrder g) kappa G ∧
      (L : ℝ) <
          max 0 (Real.logb 3
            (shiftedTailAbsorptionPrefactor d
              (midpointResponseOrder g) (printRowOrder g) G) / kappa) + 1 ∧
      (∀ Q : TriadicCube d,
        (aRef.coeffOn Q).toCoeffField =
          affineCoefficient (Selection.normalizedRoot (symmPart abar))
            ((Matrix.isUnit_iff_isUnit_det _).mp
              (normalizedRoot_posDef_of_posDef hS).isUnit)
            ⇑(normalizedCenteredCoeff a abar hS).1) ∧
      ScalarIdentityPowerTail aRef (midpointResponseOrder g)
        (Real.sqrt delta) (kappa / 2)
          ((3 : ℝ) ^
            ((Quenched.triadicCeilingIndex (X a) + L : ℕ) : ℤ)) := by
  have hmargins := Certificate.printOrder_margins hg
  exact
    Certificate.exists_formulaicShiftedNormalizedReferencePowerTail_of_hasAllLaterPhysicalBlockRow
      a abar hS (midpointResponseOrder g) (printRowOrder g) kappa delta S X
        hmargins.2.2.1 hmargins.2.2.2.1
        (printRowOrder_lt_twice_midpointResponseOrder hg) hkappa hdelta hrow
        hXone hburn

end

end RowSupply
end HighContrast
end HCPolySupport
