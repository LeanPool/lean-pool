/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousChart
public import LeanPool.CCDN.AuxiliaryPolynomial.Nonmultiple
public import LeanPool.CCDN.Determinant.HeightDeterminant
public import LeanPool.CCDN.Height.CountingHypotheses
import LeanPool.CCDN.Algebra.HomogeneousRankDichotomy
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryDegree
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryLargeHeight
import LeanPool.CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary
import LeanPool.CCDN.Determinant.HomogeneousDeterminantComparison
import LeanPool.CCDN.Determinant.ProjectiveHeightDeterminant

/-!
Homogeneous auxiliary polynomials for bounded primitive projective points,
with explicit degrees in both coefficient-height ranges.

The coefficient-sensitive determinant comparison for bounded primitive
integer representatives of projective plane points.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem projective_no_auxiliary_height_comparison
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 2 ≤ d) (hdM : d ≤ M)
    {H : ℝ} (hchart : IsBoundedPlaneCurve K (affineChart 2 f) d H)
    {B : ℝ} {z : Fin t → IntPoint 3} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, eval (z i) g = 0) → f ∣ g) :
    ∃ s : ℕ, 0 < s ∧ s + (2 + (M - d)).choose (M - d) = (2 + M).choose M ∧
      2 * s + d ^ 2 = d * (2 * M + 3) ∧
      (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
        Real.log (1 + Real.log H / (d : ℝ) ^ 2) -
          heightDeterminantError projectivePlaneDeterminantConstant) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
          s * M * Real.log B -
          (((2 + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨s, a, _, _, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM z hzB.eval_eq_zero
      hzB.one_le_radius hzB.abs_le hrel
  have hs := (plane_homogeneous_rank_bounds (by omega : 0 < d) hdM hr).1
  refine ⟨s, hs, hr, plane_homogeneous_rank_identity hdM hr, ?_⟩
  let F := fun j => (monomial (homogeneousMonomials 2 M j) 1 : MvPolynomial (Fin 3) ℤ)
  have hF : ∀ j, (F j).IsHomogeneous M := fun j =>
    isHomogeneous_monomial _ (homogeneousMonomials_degree 2 M j)
  have he : (Matrix.of fun i j => eval ((z ∘ a) i) (F j)) =
      evaluationMatrix (homogeneousMonomials 2 M) (z ∘ a) := by
    ext i j
    simp [F, evaluationMatrix, eval_monomial]
  have hi' : LinearIndependent ℚ
      ((Matrix.of fun i j => eval ((z ∘ a) i) (F j)).map ((↑) : ℤ → ℚ)).row := by
    rw [he]
    exact hi
  have hlower := projective_determinant_log_lower_height (z := z ∘ a) hs f hf hd hchart
    ⟨hF, fun i => hzB.primitive (a i), fun i => hzB.eval_eq_zero (a i), hi'⟩
  rw [he] at hlower
  exact hlower.trans hupper

end
end CCDN

namespace CCDN
noncomputable section

private theorem projective_exists_auxiliary_small_height
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 2 ≤ d) (hdM : d ≤ M)
    {H : ℝ} (hchart : IsBoundedPlaneCurve F (affineChart 2 f) d H)
    {B : ℝ} {z : Fin t → IntPoint 3} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (hML : Real.log B ≤ M)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B)
    (hthreshold : 2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) *
      (d : ℝ) ^ 3 * (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
        |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) < M) :
    ∃ g, IsPointAuxiliary f g M z := by
  classical
  by_contra hnone
  obtain ⟨s, _, _, hr, hc⟩ := projective_no_auxiliary_height_comparison
    order f hf hf0 hd hdM hchart hzB (dvd_of_not_exists_isPointAuxiliary hnone)
  have hH := hchart.one_le_height
  have hB := hzB.one_le_radius
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hlog := plane_auxiliary_log_degree_bound (by omega : 0 < d) hdM hr hB hL hML hheight hc
  have hA : 0 < 1 + Real.log H / (d : ℝ) ^ 2 := by
    have := Real.log_nonneg hH
    positivity
  have hbound := plane_degree_bound_of_log_bound (by omega : 0 < d) (by omega : 0 < M)
    (by linarith) (by linarith) hA hlog
  exact (not_lt_of_ge hbound) hthreshold

private theorem projective_exists_auxiliary_large_height
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 2 ≤ d) (hMlarge : 32 * d ≤ M)
    {H : ℝ} (hchart : IsBoundedPlaneCurve F (affineChart 2 f) d H)
    {B : ℝ} {z : Fin t → IntPoint 3} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2)
    (hthreshold :
      8 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 6 + T) *
        (d : ℝ) ^ 3 < M) :
    ∃ g, IsPointAuxiliary f g M z := by
  classical
  have hdM : d ≤ M := by omega
  by_contra hnone
  obtain ⟨s, _, _, hr, hc⟩ := projective_no_auxiliary_height_comparison
    order f hf hf0 hd hdM hchart hzB (dvd_of_not_exists_isPointAuxiliary hnone)
  have hH := hchart.one_le_height
  have hB := hzB.one_le_radius
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hlog := plane_auxiliary_large_height_log_bound (by omega : 0 < d) hMlarge hr hB hL hH hT
    hheight hposition hc
  have hbound := plane_large_degree_bound_of_log_bound (by omega : 0 < d) (by omega : 0 < M) hlog
  exact (not_lt_of_ge hbound) hthreshold

/-- Small-height auxiliary form for a projective plane curve: if `f` is an integral ternary form of
degree `d ≥ 2` whose affine chart is a bounded plane curve of height `H`, `z` is a family of
primitive integral zeros of `f` in the box of radius `B`, and the leading coefficient of `f` has
logarithm at most `4 d log B`, then there is an auxiliary form of explicitly bounded degree `M`
through all the points `z i`. -/
theorem projective_auxiliary_small_height_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 2 ≤ d)
    {H : ℝ} (hchart : IsBoundedPlaneCurve F (affineChart 2 f) d H)
    {B : ℝ} {z : Fin t → IntPoint 3} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B) :
    ∃ M : ℕ, (M : ℝ) ≤ d + Real.log B +
      2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
          |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) + 2 ∧
      ∃ g, IsPointAuxiliary f g M z := by
  let R := 2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) *
    (d : ℝ) ^ 3 * (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
      |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2)
  have hB := hzB.one_le_radius
  have hR : 0 ≤ R := by
    have := Real.log_nonneg hchart.one_le_height
    have hB0 : 0 ≤ B := by linarith
    dsimp only [R]
    positivity
  obtain ⟨M, hdM, hML, hth, hM⟩ := auxiliary_integer_degree_selection d (Real.log_nonneg hB) hR
  refine ⟨M, hM, ?_⟩
  exact projective_exists_auxiliary_small_height order f hf hf0 hd hdM hchart hzB hML hheight hth

/-- Large-height auxiliary form for a projective plane curve: if `f` is an integral ternary form of
degree `d ≥ 2` whose affine chart is a bounded plane curve of height `H`, `z` is a family of
primitive integral zeros of `f` in the box of radius `B`, `4 d log B ≤ log H`, and `H` is at
most the leading coefficient of `f` times `exp (T d²)`, then there is an auxiliary form through
all the points `z i` of degree at most
`(34 + 8 exp (heightDeterminantError projectivePlaneDeterminantConstant + 6 + T)) d³`. -/
theorem projective_auxiliary_large_height_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 2 ≤ d)
    {H : ℝ} (hchart : IsBoundedPlaneCurve F (affineChart 2 f) d H)
    {B : ℝ} {z : Fin t → IntPoint 3} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2) :
    ∃ M : ℕ, (M : ℝ) ≤
        (34 + 8 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 6 + T)) *
          (d : ℝ) ^ 3 ∧
      ∃ g, IsPointAuxiliary f g M z := by
  let R := 8 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 6 + T) *
      (d : ℝ) ^ 3
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  obtain ⟨M, hMlarge, _, hth, hM⟩ := auxiliary_integer_degree_selection (32 * d)
    (show (0 : ℝ) ≤ 0 from le_rfl) hR
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hd31 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := le_trans hd1 hd3
  refine ⟨M, ?_, ?_⟩
  · dsimp only [R] at hM
    push_cast at hM
    nlinarith
  · exact projective_exists_auxiliary_large_height order f hf hf0 hd hMlarge hchart hzB T hT
      hheight hposition hth

end
end CCDN
