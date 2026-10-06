/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierJApproximationOrthogonality

/-!
# The heat range in the Leray data space

The heat multiplier preserves the divergence-free Fourier condition, which
places the real heat evolution of initial data in `J`.
-/

public section

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The real heat semigroup preserves the Leray data space `J`. -/
theorem realHeatOperator_isInJ {t : ℝ} (ht : 0 ≤ t) (f : RealVectorL2)
    (hf : CKN.IsInJ (realVectorL2Representative f)) :
    CKN.IsInJ (realVectorL2Representative (realHeatOperator t ht f)) := by
  exact realHeatOperator_isInJ_of_fourierOrthogonal t ht f
    (realVectorL2_fourierOrthogonal_of_isInJ f hf)

end CKN.Leray

end
