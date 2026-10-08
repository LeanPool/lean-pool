/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryLayer

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexBoundaryDistance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Euclidean distance to the complement of a domain

The project vector carrier has the supremum norm. Fractional boundary weights
use Euclidean distance, so the distance is taken in the project's Hilbert
realization while retaining the ambient `Vec` carrier.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Euclidean distance from `x` to the complement of `U`. On an open domain
this is the Euclidean distance to its boundary. -/
@[expose]
noncomputable def euclideanBoundaryDistance (U : Set (Vec d)) (x : Vec d) : ℝ :=
  Metric.infDist (HilbertVec.ofVec x) (HilbertVec.ofVec '' Uᶜ)

theorem euclideanBoundaryDistance_nonneg (U : Set (Vec d)) (x : Vec d) :
    0 ≤ euclideanBoundaryDistance U x :=
  Metric.infDist_nonneg

theorem continuous_euclideanBoundaryDistance (U : Set (Vec d)) :
    Continuous (euclideanBoundaryDistance U) := by
  exact (Metric.continuous_infDist_pt (HilbertVec.ofVec '' Uᶜ)).comp
    (HilbertVec.ofVecL d).continuous

theorem measurable_euclideanBoundaryDistance (U : Set (Vec d)) :
    Measurable (euclideanBoundaryDistance U) :=
  (continuous_euclideanBoundaryDistance U).measurable

theorem euclideanBoundaryDistance_le_of_not_mem {U : Set (Vec d)}
    {x y : Vec d} (hy : y ∉ U) :
    euclideanBoundaryDistance U x ≤ euclideanDist x y := by
  unfold euclideanBoundaryDistance
  have himage : HilbertVec.ofVec y ∈ HilbertVec.ofVec '' Uᶜ :=
    ⟨y, hy, rfl⟩
  calc
    Metric.infDist (HilbertVec.ofVec x) (HilbertVec.ofVec '' Uᶜ)
        ≤ dist (HilbertVec.ofVec x) (HilbertVec.ofVec y) :=
      Metric.infDist_le_dist_of_mem himage
    _ = euclideanDist x y := by
      rw [dist_eq_norm, ← euclideanDist_eq_norm_sub_ofVec]

theorem euclideanBallAt_subset_of_le_boundaryDistance {U : Set (Vec d)}
    {x : Vec d} {r : ℝ} (hr : 0 ≤ r)
    (hreach : r ≤ euclideanBoundaryDistance U x) :
    euclideanBallAt x r ⊆ U := by
  intro y hy
  by_contra hyU
  have hdist : euclideanDist x y < r := by
    rw [← Real.sqrt_sq hr, euclideanDist, euclideanNorm,
      Real.sqrt_lt_sqrt_iff (vecNormSq_nonneg (x - y))]
    have hsymm : vecNormSq (x - y) = vecNormSq (y - x) := by
      rw [show x - y = -(y - x) by abel, vecNormSq_neg]
    rw [hsymm]
    exact hy
  exact (not_lt_of_ge hreach)
    ((euclideanBoundaryDistance_le_of_not_mem hyU).trans_lt hdist)

theorem not_subset_euclideanBallAt_of_boundaryDistance_lt {U : Set (Vec d)}
    (hcomp : Uᶜ.Nonempty) {x : Vec d} {r : ℝ} (hr : 0 ≤ r)
    (hreach : euclideanBoundaryDistance U x < r) :
    ¬euclideanBallAt x r ⊆ U := by
  have himage : (HilbertVec.ofVec '' Uᶜ).Nonempty := hcomp.image _
  unfold euclideanBoundaryDistance at hreach
  rw [Metric.infDist_lt_iff himage] at hreach
  obtain ⟨z, hz, hxz⟩ := hreach
  obtain ⟨y, hy, rfl⟩ := hz
  refine Set.not_subset.mpr ⟨y, ?_, hy⟩
  have hxy : euclideanDist x y < r := by
    rwa [dist_eq_norm, ← euclideanDist_eq_norm_sub_ofVec] at hxz
  rw [mem_euclideanBallAt_iff]
  have hsq : vecNormSq (x - y) < r ^ 2 := by
    rwa [euclideanDist, euclideanNorm, ← Real.sqrt_sq hr,
      Real.sqrt_lt_sqrt_iff (vecNormSq_nonneg (x - y))] at hxy
  rwa [show y - x = -(x - y) by abel, vecNormSq_neg]

end

end HighContrast
end HCPolySupport
