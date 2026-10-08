/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.RealTranslationCoeffSpace
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedNormalizedRootDoubledResponseSubadditivity
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Translation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.RealTranslationDoubledResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Real-translation covariance of the doubled response

The deterministic coarse response is covariant under every Euclidean
translation.  No invariance of a probability law is asserted here.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Coarse blocks on a translated set are coarse blocks of the deterministically
translated coefficient sample. -/
theorem coarseBlock_translateSet_real (z : Vec d) (U : Set (Vec d))
    (a : CoeffSpace d) :
    coarseBlock (translateSet z U) a =
      coarseBlock U (realTranslateCoeff z a) := by
  rw [coarseBlock_eq_of_ae_eq (U := U) (realTranslateCoeff z a)
    (realTranslateCoeff_ae z a)]
  exact coarseBlockMatrix_translateSet_eq_translateCoeffField z U (⇑a.1)

/-- The coefficient-space doubled response is covariant under arbitrary real
translations. -/
theorem coeffSpaceDoubledResponse_translateSet_real
    (z : Vec d) (U : Set (Vec d)) (a : CoeffSpace d) (P Q : BlockVec d) :
    Transport.coeffSpaceDoubledResponse (translateSet z U) a P Q =
      Transport.coeffSpaceDoubledResponse U (realTranslateCoeff z a) P Q := by
  unfold Transport.coeffSpaceDoubledResponse
  rw [coarseBlock_translateSet_real]
  simp only [Transport.coarseStarInv_eq_blockReflect]
  rw [coarseBlock_translateSet_real]

end

end RowSupply
end HighContrast
end HCPolySupport
