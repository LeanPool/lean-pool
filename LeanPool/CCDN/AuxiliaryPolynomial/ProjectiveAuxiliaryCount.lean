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
import LeanPool.CCDN.Algebra.HomogeneousChartIrreducible
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.AuxiliaryPolynomial.ProjectiveAuxiliary
import LeanPool.CCDN.Plane.ProjectivePlaneBezout

/-! Projective point counts obtained from integral homogeneous
auxiliary polynomials and projective Bézout. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem projective_integer_points_card_le_auxiliary_degree {d M t : ℕ}
    (f g : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (hprim : PrimitiveIntegerPolynomial f) (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (z : Fin t → IntPoint 3) (hz0 : ∀ i, z i ≠ 0)
    (hinj : Function.Injective (fun i => Projectivization.mk ℚ (rationalPoint (z i))
      (rationalPoint_ne_zero (hz0 i))))
    (hzf : ∀ i, eval (z i) f = 0) (hg : IsPointAuxiliary f g M z) :
    t ≤ d * M := by
  have hndQ : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g :=
    fun h => hg.not_dvd (hprim.rational_map_dvd_iff.mp h)
  have hzero (q : MvPolynomial (Fin 3) ℤ) {m : ℕ} (hq : q.IsHomogeneous m)
      (hzq : ∀ i, eval (z i) q = 0) (i : Fin t) :
      Projectivization.mk ℚ (rationalPoint (z i)) (rationalPoint_ne_zero (hz0 i)) ∈
        projectiveZeroLocus (map (Int.castRingHom ℚ) q) := by
    rw [mem_projectiveZeroLocus_mk (hq.map _)]
    change eval ((Int.castRingHom ℚ) ∘ z i) (map (Int.castRingHom ℚ) q) = 0
    rw [← map_eval, hzq i, map_zero]
  simpa only [Fintype.card_fin] using projective_plane_common_zeros_card_le
    _ _ (hf.map _) hir (hg.isHomogeneous.map _) hndQ _ hinj (hzero f hf hzf)
    (hzero g hg.isHomogeneous hg.eval_eq_zero)

private theorem projective_chart_rational_irreducible
    {K : Type*} [Field K] [CharZero K] {d : ℕ}
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (hdeg : (affineChart 2 f).totalDegree = d)
    (hir : Irreducible (map (Int.castRingHom K) (affineChart 2 f))) :
    Irreducible (map (Int.castRingHom ℚ) f) := by
  apply irreducible_of_affineChart_irreducible
  · rw [affineChart_map, rational_map_totalDegree, rational_map_totalDegree,
      hdeg, hf.totalDegree hf0]
  · rw [affineChart_map]
    exact rational_irreducible_of_charZero_map _ hir

/-- Small-height count of projective points on a plane curve: if `f` is a primitive integral
ternary form of degree `d ≥ 2` whose affine chart is a bounded plane curve of height `H`, and
the leading coefficient of `f` has logarithm at most `4 d log B`, then a family of primitive
integral zeros of `f` in the box of radius `B`, pairwise distinct as projective points, has at
most `d` times the small-height auxiliary degree bound members. -/
theorem projective_points_small_height_bound
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 2 ≤ d)
    (hprim : PrimitiveIntegerPolynomial f)
    {H : ℝ} (hchart : IsBoundedPlaneCurve K (affineChart 2 f) d H)
    (z : Fin t → IntPoint 3) (hz0 : ∀ i, z i ≠ 0)
    (hinj : Function.Injective (fun i => Projectivization.mk ℚ (rationalPoint (z i))
      (rationalPoint_ne_zero (hz0 i))))
    {B : ℝ} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B) :
    (t : ℝ) ≤ d * (d + Real.log B +
      2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
          |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) + 2) := by
  obtain ⟨M, hM, g, hg⟩ := projective_auxiliary_small_height_degree
    order f hf hf0 hd hchart hzB hheight
  have h := projective_integer_points_card_le_auxiliary_degree f g hf hprim
    (projective_chart_rational_irreducible f hf hf0 hchart.totalDegree_eq hchart.irreducible)
    z hz0 hinj hzB.eval_eq_zero hg
  have hR : (t : ℝ) ≤ d * (M : ℝ) := by exact_mod_cast h
  exact hR.trans (mul_le_mul_of_nonneg_left hM (by positivity))

/-- Large-height count of projective points on a plane curve: if `f` is a primitive integral
ternary form of degree `d ≥ 2` whose affine chart is a bounded plane curve of height `H`, with
`4 d log B ≤ log H` and `H` at most the leading coefficient of `f` times `exp (T d²)`, then a
family of primitive integral zeros of `f` in the box of radius `B`, pairwise distinct as
projective points, has at most
`(34 + 8 exp (heightDeterminantError projectivePlaneDeterminantConstant + 6 + T)) d⁴` members. -/
theorem projective_points_large_height_bound
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 2 ≤ d)
    (hprim : PrimitiveIntegerPolynomial f)
    {H : ℝ} (hchart : IsBoundedPlaneCurve K (affineChart 2 f) d H)
    (z : Fin t → IntPoint 3) (hz0 : ∀ i, z i ≠ 0)
    (hinj : Function.Injective (fun i => Projectivization.mk ℚ (rationalPoint (z i))
      (rationalPoint_ne_zero (hz0 i))))
    {B : ℝ} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (T : ℝ) (hT : 0 ≤ T) (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2) :
    (t : ℝ) ≤
      (34 + 8 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 6 + T)) *
        (d : ℝ) ^ 4 := by
  obtain ⟨M, hM, g, hg⟩ := projective_auxiliary_large_height_degree
    order f hf hf0 hd hchart hzB T hT hheight hposition
  have h := projective_integer_points_card_le_auxiliary_degree f g hf hprim
    (projective_chart_rational_irreducible f hf hf0 hchart.totalDegree_eq hchart.irreducible)
    z hz0 hinj hzB.eval_eq_zero hg
  have hR : (t : ℝ) ≤ d * (M : ℝ) := by exact_mod_cast h
  calc
    _ ≤ d * ((34 + 8 *
          Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 6 + T)) *
        (d : ℝ) ^ 3) :=
      hR.trans (mul_le_mul_of_nonneg_left hM (by positivity))
    _ = _ := by ring

end
end CCDN
