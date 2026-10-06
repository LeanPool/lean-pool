/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.EuclideanBallDistance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Euclidean balls in distance form
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- Membership in `euclideanBallAt` is equivalently a strict Euclidean
distance bound when the radius is positive. -/
theorem mem_euclideanBallAt_iff_euclideanDist_lt
    {c x : Vec d} {r : ℝ} (hr : 0 < r) :
    x ∈ euclideanBallAt c r ↔ euclideanDist x c < r := by
  rw [mem_euclideanBallAt_iff, ← euclideanDist_sq]
  constructor
  · intro h
    nlinarith only [h, euclideanDist_nonneg x c, hr]
  · intro h
    nlinarith only [h, euclideanDist_nonneg x c, hr]

end

end HighContrast
end HCPolySupport
