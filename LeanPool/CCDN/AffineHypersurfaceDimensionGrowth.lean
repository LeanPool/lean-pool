/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Statements
import LeanPool.CCDN.Hypersurface.AffineHypersurfaceCount

/-! CCDN Theorem 4 with the corrected degree exponent of Remark 4.3.8.
In `N = n + 3` variables the exponent is `18 + 3n = 3N + 9`: the corrected surface
bound `d^18` and a cost of `d^3` for each bounded good hyperplane slice
(`affineHypersurfaceGrowth`, in `CCDN.Hypersurface.AffineHypersurfaceCount`). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- CCDN Theorem 4 for integer equations in all affine ambient dimensions
at least three. The constant depends only on dimension, and the explicit
degree exponent is 18 + 3n in n+3 variables. -/
theorem affine_hypersurface_dimension_growth (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 3 * n) * B ^ (n + 1) :=
  affineHypersurfaceGrowth n

/-- CCDN Theorem 4 for rational equations, with the degree exponent 18 + 3n in
n+3 variables. -/
theorem affine_hypersurface_dimension_growth_rat (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℚ,
      HasAbsIrreducibleTopFormRat f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus f) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 3 * n) * B ^ (n + 1) :=
  (affineHypersurfaceGrowth n).rational

end
end CCDN
