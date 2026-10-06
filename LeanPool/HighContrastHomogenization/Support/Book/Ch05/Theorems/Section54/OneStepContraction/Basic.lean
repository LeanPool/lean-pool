/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section54.GoodScale
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale

/-!
# Coarse-graining support: Support.Book.Ch05.Theorems.Section54.OneStepContraction.Basic

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

noncomputable section

/-!
# Basic definitions for the one-step contraction

This file contains only the scalar abbreviations used by the Section 5.4
one-step contraction proof.  The theorem-facing statement remains in the final
assembly file.
-/

/-- The internal manuscript choice `epsilon = delta^(1/4)`. -/
@[expose]
noncomputable def oneStepContractionEpsilon (delta : ℝ) : ℝ :=
  Real.rpow delta (1 / 4 : ℝ)

/-- The scalar coefficient combination multiplying the additivity-defect sum
in the Section 5.3 coarse-fluctuation estimate. -/
@[expose]
noncomputable def oneStepScalarWeightAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℕ) : ℝ :=
  sigmaHatAtScale hP hStruct (m : ℤ) *
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
    (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
      hP.barSigmaAtScale hStruct 0

/-- The one-step scalar weight is the sum of the two good-scale scalar
comparisons used in the manuscript proof. -/
theorem oneStepScalarWeightAtScale_eq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℕ) :
    oneStepScalarWeightAtScale hP hStruct m =
      sigmaHatAtScale hP hStruct (m : ℤ) *
          (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
        (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
          hP.barSigmaAtScale hStruct 0 := by
  rfl

end

end OneStepContraction
end Section54
end Ch05
end Book
end HCPolySupport
