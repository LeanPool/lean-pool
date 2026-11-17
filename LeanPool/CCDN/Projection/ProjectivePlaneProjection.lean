/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ProjectiveChartIdeal
public import LeanPool.CCDN.Projection.DegreePreservingProjectionBox
import LeanPool.CCDN.Determinant.PolynomialMapDeterminant
import LeanPool.CCDN.Height.ProjectiveIntegerHeight
import LeanPool.CCDN.Projection.DegreePreservingProjectionBox

/-! The bounded integral affine projection lifts to a projective plane
map on the standard chart, with the same polynomial height factor. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For an integer vector `z` with `z 0 ≠ 0`, the projective point `[1 : z 1 / z 0 : …]` is the
point with homogeneous coordinates `z`. -/
lemma affineProjectivePoint_eq_integer {n : ℕ} (z : IntPoint (n + 1)) (hz0 : z 0 ≠ 0) :
    affineProjectivePoint (fun j => (z j.succ : ℚ) / (z 0 : ℚ)) =
      Projectivization.mk ℚ (rationalPoint z)
        (rationalPoint_ne_zero (fun h => hz0 (congrFun h 0))) := by
  have h0 : (z 0 : ℚ) ≠ 0 := by exact_mod_cast hz0
  apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr
  refine ⟨(z 0 : ℚ)⁻¹, ?_⟩
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [rationalPoint, h0]
  · simp [rationalPoint, div_eq_mul_inv, mul_comm]

/-- The map from `ℙⁿ` to the projective plane on the chart `X₀ ≠ 0`, sending a point with affine
coordinates `x` to `[1 : m₀(x) : m₁(x)]`, where `m₀`, `m₁` are the moment coordinates with
parameters `k₀` and `k₁`. -/
def projectivePlaneChartProjection {n : ℕ} (k₀ k₁ : ℕ) (x : ProjectivePoint n) :
    ProjectivePoint 2 :=
  affineProjectivePoint
    ![eval (projectiveAffineCoordinates x) (momentCoordinate ℚ n k₀),
      eval (projectiveAffineCoordinates x) (momentCoordinate ℚ n k₁)]

/-- For parameters `k₀ ≤ n ^ 2 * d` and `k₁ ≤ n * d ^ 2`, the plane chart projection of a point on
the chart `X₀ ≠ 0` of height at most `B ≥ 1` has height at most `projectionBoxFactor n d * B`. -/
theorem projectivePlaneChartProjection_height {n d k₀ k₁ : ℕ}
    (hk₀ : k₀ ≤ n ^ 2 * d) (hk₁ : k₁ ≤ n * d ^ 2)
    (x : ProjectivePoint n) (hx : x.rep 0 ≠ 0) {B : ℝ} (hB : 1 ≤ B)
    (hxB : x.mulHeight ≤ B) :
    (projectivePlaneChartProjection k₀ k₁ x).mulHeight ≤ projectionBoxFactor n d * B := by
  let z := primitiveProjectiveRep x
  obtain ⟨hz0, hchart⟩ := primitiveProjectiveRep_chart x hx
  let w : IntPoint 3 := Fin.cons (z 0) (degreeProjection n k₀ k₁ (fun j => z j.succ))
  have hw0 : w 0 ≠ 0 := hz0
  have hcoord (k : ℕ) :
      eval (projectiveAffineCoordinates x) (momentCoordinate ℚ n k) =
        (eval (fun j => z j.succ) (momentCoordinate ℤ n k) : ℚ) / (z 0 : ℚ) := by
    rw [hchart, rationalPoint_moment_eval, momentCoordinate_eval, momentCoordinate_eval,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    simp only [rationalPoint, z]
    ring
  have himage : projectivePlaneChartProjection k₀ k₁ x =
      affineProjectivePoint (fun j => (w j.succ : ℚ) / (w 0 : ℚ)) := by
    unfold projectivePlaneChartProjection
    congr 1
    funext j
    fin_cases j <;> exact hcoord _
  rw [himage, affineProjectivePoint_eq_integer w hw0]
  apply projective_integer_height_le w (fun h => hw0 (congrFun h 0))
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · change |(z 0 : ℝ)| ≤ _
    exact ((primitiveProjectiveRep_bound x 0).trans hxB).trans
      (le_mul_of_one_le_left (by linarith) (projectionBoxFactor_one_le n d))
  · have hzbox : (fun j => z j.succ) ∈ integerBox n B :=
      mem_integerBox.mpr (fun j => (primitiveProjectiveRep_bound x j.succ).trans hxB)
    exact mem_integerBox.mp (degreeProjection_box hk₀ hk₁ (by linarith) hzbox) k

/-- If the moment coordinates satisfy the plane relation `f` of degree `d` on the affine chart of
the prime `I` (with `X 0 ∉ I`), then the plane chart projection maps the points of the projective
variety of `I` on the chart `X₀ ≠ 0` into the projective plane curve defined by the homogenization
of `f`. -/
theorem projectivePlaneChartProjection_zero {n d k₀ k₁ : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime] (hX : X 0 ∉ I)
    (f : MvPolynomial (Fin 2) ℚ) (hfd : f.totalDegree = d)
    (hfI : aeval ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] f ∈ projectiveChartIdeal I)
    (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) (hx0 : x.rep 0 ≠ 0) :
    projectivePlaneChartProjection k₀ k₁ x ∈
      projectiveZeroLocus (scaledHomogenize d 1 f) := by
  have hh := projectiveChartIdeal_point I hX x hx hx0 _ hfI
  rw [eval_polynomial_coordinate_map] at hh
  change affineProjectivePoint _ ∈ _
  unfold affineProjectivePoint
  rw [mem_projectiveZeroLocus_mk (scaledHomogenize_homogeneous 1 f hfd.le),
    ← affineChart_eval, affineChart_scaledHomogenize_one]
  convert hh using 1
  congr 2
  funext j
  fin_cases j <;> rfl

end
end CCDN
