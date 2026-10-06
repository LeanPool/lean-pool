/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryDistanceLipschitz
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryWeightMoment

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexBoundaryWeightNearComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Boundary-weight comparison near an interior point
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Inside half the boundary distance from `x`, boundary distance remains at
least half its value at `x`. -/
theorem half_euclideanBoundaryDistance_le_of_mem_ball
    (U : Set (Vec d)) {x y : Vec d}
    (hx : 0 < euclideanBoundaryDistance U x)
    (hy : y ∈ euclideanBallAt x (euclideanBoundaryDistance U x / 2)) :
    euclideanBoundaryDistance U x / 2 ≤ euclideanBoundaryDistance U y := by
  have hlip := euclideanBoundaryDistance_le_add_euclideanDist U x y
  have hsq : euclideanDist y x ^ 2 <
      (euclideanBoundaryDistance U x / 2) ^ 2 := by
    simpa only [mem_euclideanBallAt_iff, euclideanDist_sq] using hy
  have hdist' : euclideanDist y x < euclideanBoundaryDistance U x / 2 := by
    nlinarith only [hsq, euclideanDist_nonneg y x, hx]
  have hdist : euclideanDist x y < euclideanBoundaryDistance U x / 2 := by
    rwa [euclideanDist_comm] at hdist'
  linarith only [hlip, hdist]

/-- A negative boundary-distance weight is uniformly controlled on the ball
of half the center boundary distance. -/
theorem euclideanBoundaryWeight_le_of_mem_half_ball
    (U : Set (Vec d)) {p : ℝ} (hp : 0 ≤ p) {x y : Vec d}
    (hx : 0 < euclideanBoundaryDistance U x)
    (hy : y ∈ euclideanBallAt x (euclideanBoundaryDistance U x / 2)) :
    euclideanBoundaryWeight U p y ≤
      ENNReal.ofReal ((euclideanBoundaryDistance U x / 2) ^ (-p)) := by
  unfold euclideanBoundaryWeight
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (half_euclideanBoundaryDistance_le_of_mem_ball U hx hy)
    (neg_nonpos.mpr hp)

end

end HighContrast
end HCPolySupport
