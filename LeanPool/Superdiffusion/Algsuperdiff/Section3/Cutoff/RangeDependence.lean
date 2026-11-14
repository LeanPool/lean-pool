/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# RangeDependence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The natural spatial range of the actual cutoff law

ABK26 records that the lower-infinite cutoff `k_m`, and hence the actual
coefficient `a_m = nu I + k_m`, has dependence range `sqrt(d) * 3^m`.  This file
owns that literal scale vocabulary.  The proof of independence itself is
intentionally downstream of the local-limit A: it must show that the *actual*
`Cutoff.coefficientCutoffLaw` reads only the lower-shell restriction
sigma-field, and then combine J1 with the prefix's cross-shell independence.  It
must not be replaced by an assumption on a free coefficient law.  -/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport

noncomputable section

/-- The exact spatial dependence range of the actual cutoff at shell scale `m`, as
stated in ABK26.  This is the Euclidean range used by J1; the later proof converts
it to CoarseGraining's ambient unit-range condition only after a triadic scale
normalization. -/
def cutoffNaturalRange (d : ℕ) (m : ℤ) : ℝ :=
  Real.sqrt (d : ℝ) * (3 : ℝ) ^ m

/-- At scale zero the natural range is exactly `sqrt d`, matching the J1
normalization of the zero shell. -/
@[simp]
theorem cutoffNaturalRange_zero (d : ℕ) : cutoffNaturalRange d 0 = Real.sqrt d := by
  simp [cutoffNaturalRange]

end

end Algsuperdiff.Section3.Cutoff
