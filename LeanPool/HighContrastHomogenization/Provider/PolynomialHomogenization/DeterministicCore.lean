/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.DeterministicNormalization
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.Duality
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.GeneralCoarseGrainingL2TwoExponent

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.DeterministicCore

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Law-free deterministic coarse comparison

The Chapter 3 two-exponent comparison is specialized to the normalized
identity background.  Its only quantitative input is the displayed
deterministic coarse right-hand side; no probability law occurs here.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- The proved Chapter 3 comparison specialized to the normalized identity
background. -/
theorem exists_normalizedCubeNegativeBesovComparisonConstant
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : Book.Ch03.CoeffFamily d}
        {s r r₂ : ℝ} {j : ℕ} {g : Vec d → Vec d}
        (w : Book.Ch03.CoarseGrainingComparisonDatum Q a
          (identityConstantCoeffMatrix d) g),
        0 < s → 0 < r → r < s / 2 → s < 1 → r ≤ r₂ →
          Book.Ch03.ForceBesovRegularity Q r₂ g →
          Book.Ch03.homogenizationComparisonNegativeBesovLHS Q a
              (identityConstantCoeffMatrix d) s w.u w.v ≤
            Book.Ch03.generalCoarseGrainingL2TwoExponentRHS C Q a
              (identityConstantCoeffMatrix d) s r r₂ j g w.u := by
  rcases (Book.Ch03.generalCoarseGrainingL2TwoExponentTheory d).exists_constant with
    ⟨C, hC, hcomparison⟩
  refine ⟨C, hC, ?_⟩
  intro Q a s r r₂ j g w hs hr hrs hs_lt hrr₂ hg
  exact hcomparison (identityConstantCoeffMatrix_isPositiveScalarMatrix d) w
    hs hr hrs hs_lt hrr₂ hg

end

end HighContrast
end HCPolySupport
