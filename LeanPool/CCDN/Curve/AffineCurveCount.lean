/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Statements
import LeanPool.CCDN.Plane.CurveCount
import LeanPool.CCDN.Projection.AffineProjectionCount
import LeanPool.CCDN.Projection.ScaleAbsorption

/-! The coefficient-uniform affine curve count of CCDN Theorem 3. A bounded integral projection
reduces a curve in `𝔸ⁿ` to an irreducible plane equation of the same degree, whose points the
plane bound `PlaneCurveBound` counts; exceptional fibres contribute at most `d(d − 1)` points and
the enlarged box costs a constant depending only on `n`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The affine curve counting bound `AffineCurveBound` of CCDN Theorem 3: the plane bound, after
a degree-preserving bounded projection to the plane. -/
theorem affine_curve_count : AffineCurveBound := by
  obtain ⟨C, hC, hplane⟩ := planeCurveBound
  intro n _hn
  let K := Real.exp (projectionLogConstant n) * (projectionLogConstant n + 1)
  have hK : 0 < K := by
    have := projectionLogConstant_nonneg n
    dsimp [K]
    positivity
  refine ⟨C * K + 1, by positivity, ?_⟩
  intro I hI d hd hdegree B hB
  have : I.IsPrime := hI
  obtain ⟨f, hf, hfd, hred⟩ := exists_plane_count_reduction I d hd hdegree
  have hbox : 1 ≤ projectionBoxFactor n d * B :=
    one_le_mul_of_one_le_of_one_le (projectionBoxFactor_one_le n d) hB
  have hp := hplane f hf (hfd.symm ▸ hd) _ hbox
  rw [hfd] at hp
  have hredR : (count (idealZeroLocus I) B : ℝ) ≤
      count (zeroLocus f) (projectionBoxFactor n d * B) + (d * (d - 1) : ℕ) := by
    exact_mod_cast hred B hB
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have herr : ((d * (d - 1) : ℕ) : ℝ) ≤ curveBound d B := by
    calc
      _ ≤ (d : ℝ) ^ 2 := by
        exact_mod_cast (show d * (d - 1) ≤ d ^ 2 by
          simpa only [pow_two] using Nat.mul_le_mul_left d (Nat.sub_le d 1))
      _ ≤ (d : ℝ) ^ 4 := by nlinarith [one_le_pow₀ hd1 (n := 2), sq_nonneg ((d : ℝ) ^ 2 - 1)]
      _ ≤ _ := degree_four_le_curveBound hd hB
  calc
    _ ≤ (count (zeroLocus f) (projectionBoxFactor n d * B) : ℝ) + (d * (d - 1) : ℕ) := hredR
    _ ≤ C * curveBound d (projectionBoxFactor n d * B) + curveBound d B := add_le_add hp herr
    _ ≤ C * (K * curveBound d B) + curveBound d B := by
      exact add_le_add (mul_le_mul_of_nonneg_left (projection_curveBound_scale n hd hB) hC.le)
        le_rfl
    _ = _ := by ring


end
end CCDN
