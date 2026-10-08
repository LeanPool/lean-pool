/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierPhysicalRange
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit

/-!
# The Leray and Stokes ranges in the initial-data space

The physical weak-divergence conclusions for the Fourier multipliers imply
membership in the closure space `J` used in `lem:reg-local-mild`.
-/

public section

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic


/-- The real heat-regularized Leray-Stokes operator takes values in `J`, as
needed for the time integral in `eq:reg-mild`. -/
theorem realStokesOperator_isInJ {t : ℝ} (ht : 0 < t)
    (F : RealTensorL2) :
    CKN.IsInJ (realVectorL2Representative (realStokesOperator ht F)) :=
  (CKN.isInJ_iff_weakDivFree).2 (realStokesOperator_isWeakDivFree ht F)

end CKN.Leray

end
