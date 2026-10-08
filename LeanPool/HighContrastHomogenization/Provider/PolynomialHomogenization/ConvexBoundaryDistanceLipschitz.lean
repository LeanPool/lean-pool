/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryDistance

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexBoundaryDistanceLipschitz

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Lipschitz control of Euclidean boundary distance
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- Boundary distance changes by at most the Euclidean distance between its
arguments. -/
theorem euclideanBoundaryDistance_le_add_euclideanDist
    (U : Set (Vec d)) (x y : Vec d) :
    euclideanBoundaryDistance U x ≤
      euclideanBoundaryDistance U y + euclideanDist x y := by
  unfold euclideanBoundaryDistance
  calc
    Metric.infDist (HilbertVec.ofVec x) (HilbertVec.ofVec '' Uᶜ) ≤
        Metric.infDist (HilbertVec.ofVec y) (HilbertVec.ofVec '' Uᶜ) +
          dist (HilbertVec.ofVec x) (HilbertVec.ofVec y) :=
      Metric.infDist_le_infDist_add_dist
    _ = Metric.infDist (HilbertVec.ofVec y) (HilbertVec.ofVec '' Uᶜ) +
        euclideanDist x y := by
      congr 1
      rw [dist_eq_norm, ← euclideanDist_eq_norm_sub_ofVec]

end

end HighContrast
end HCPolySupport
