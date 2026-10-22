/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Height.ProjectiveZeroLocus
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import LeanPool.CCDN.LowerBound.GridLowerBoundNumerics
import LeanPool.CCDN.LowerBound.GridProjectiveLowerBound
import LeanPool.CCDN.Plane.ProjectivePlaneBezout

/-! The lower bound of CCDN Proposition 5 for projective plane equations, with its exact
constant 1/5: the grid construction for degree at least four, and two rational points for
smaller degrees. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For every d>0 there is an absolutely irreducible projective plane curve
of degree d and an integer B≥1 with N(X,B)≥d² B^(2/d)/5. -/
theorem projective_plane_lower_bound (d : ℕ) (hd : 0 < d) :
    ∃ F : MvPolynomial (Fin 3) ℚ, ∃ B : ℕ, 1 ≤ B ∧
      F.IsHomogeneous d ∧ F.totalDegree = d ∧
        AbsolutelyIrreducibleRat F ∧
          ((d : ℝ) ^ 2 / 5) * (B : ℝ) ^ (2 / (d : ℝ)) ≤
            (projectiveCount (projectiveZeroLocus F) B : ℝ) := by
  by_cases hlarge : 4 ≤ d
  · obtain ⟨F, hhom, hdeg, hir, hcount⟩ := exists_projective_grid_lower_bound d hlarge
    rw [grid_lower_bound_radius_identity d hd] at hcount
    refine ⟨F, (d + 1) / 4, grid_lower_bound_radius_pos (by omega), hhom, hdeg, hir, ?_⟩
    apply (grid_square_card_lower_bound hd (by positivity)
      (grid_lower_bound_radius_size d)).trans
    exact_mod_cast hcount
  · obtain ⟨F, hhom, hdeg, hir, hcount⟩ := exists_projective_two_point_lower_bound d hd
    refine ⟨F, 1, le_rfl, hhom, hdeg, hir, ?_⟩
    have hcountR : (2 : ℝ) ≤ projectiveCount (projectiveZeroLocus F) 1 := by exact_mod_cast hcount
    have hdR : (d : ℝ) ≤ 3 := by exact_mod_cast (show d ≤ 3 by omega)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    simp only [Nat.cast_one, Real.one_rpow, mul_one]
    nlinarith [mul_nonneg hd0 (show 0 ≤ 3 - (d : ℝ) by linarith)]

end
end CCDN
