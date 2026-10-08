/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormScaleEnergy

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormScaleClosure

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Centered single-scale closure for the diagonal weak estimate

The centered child increment is bounded by finite-variance contraction and
the uncentered response estimate at the same scale.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The normalized metric square sum of the centered child averages obeys
the response-maximum scale estimate. -/
theorem diagonalWeak_scale_energy_bound [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {S m : Mat d} (hsymm : matTranspose S = S) (hsq : S * S = m)
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho : ℝ} {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) :
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w)
              (diagonalWeakState hq t a p r) -
            blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t a p r))) ≤
      Real.sqrt 2 * diagonalWeakMetricFactor m E *
        (1 + Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
          (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)) *
            diagonalWeakEnergy hq t a p r := by
  exact (blockAvsumL2_metricRoot_centered_diagonalWeakState_le
    hq hkt p r).trans (blockAvsumL2_metricRoot_diagonalWeakState_le
      hq hkt hsymm hsq hm hE hEpd p r hfinite)

end

end Response

end HighContrast

end HCPolySupport

end
