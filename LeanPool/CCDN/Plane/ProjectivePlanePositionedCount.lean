/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousChart
public import LeanPool.CCDN.Height.ProjectiveBox
public import LeanPool.CCDN.Plane.ScaledPlaneCount
import LeanPool.CCDN.Algebra.HomogeneousChartIrreducible
import LeanPool.CCDN.Algebra.ProjectiveTranslation
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.AuxiliaryPolynomial.ProjectiveAuxiliaryCount
import LeanPool.CCDN.Plane.ScaledModelPosition

/-! Coefficient-uniform projective plane counts after a bounded integral
coordinate change. The finite-field and positioning inputs are proved. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem homogeneous_absolute_chart_data
    {K : Type*} [Field K] [CharZero K] {d : ℕ}
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom K) f)) :
    (affineChart 2 f).totalDegree = d ∧
      Irreducible (map (Int.castRingHom K) (affineChart 2 f)) := by
  have hirQ := rational_irreducible_of_charZero_map f hir
  have hQ := affineChart_degree_of_not_variable_dvd _ (hf.map _)
    (variable_not_dvd_irreducible_homogeneous _ (hf.map _) hirQ hd 0)
  rw [affineChart_map, rational_map_totalDegree] at hQ
  refine ⟨hQ, ?_⟩
  rw [← affineChart_map]
  exact affineChart_irreducible_of_not_variable_dvd _ (hf.map _) hir
    (variable_not_dvd_irreducible_homogeneous _ (hf.map _) hir hd 0)

/-- Coefficient-uniform projective plane count: for a primitive ternary integer form `f` of degree
`d ≥ 2`, absolutely irreducible over an algebraically closed field of characteristic zero, the
number of distinct projective points with primitive integer coordinates in the box of size `B` on
`f = 0` is at most the maximum of the two degree bounds of the scaled plane count with residue
constant `projectivePlaneDeterminantConstant`. The proof first moves `f` by a bounded integral
coordinate change. -/
theorem projective_plane_finite_count_positioned
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d t : ℕ}
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (z : Fin t → IntPoint 3) (hz0 : ∀ i, z i ≠ 0)
    (hinj : Function.Injective (fun i => Projectivization.mk ℚ (rationalPoint (z i))
      (rationalPoint_ne_zero (hz0 i))))
    {B : ℝ} (hzB : IsPrimitiveBoxZeroFamily f B z) :
    (t : ℝ) ≤ max
      ((d : ℝ) * scaledPlaneAuxiliaryDegreeBound d projectivePlaneDeterminantConstant (((d : ℝ) +
          1) * B) 1)
      ((34 + 8 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 20)) *
          (d : ℝ) ^ 4) := by
  obtain ⟨⟨hB, hz, hbox⟩, hzprim⟩ := hzB
  have hdpos : 0 < d := by omega
  have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by simp [h])
  obtain ⟨a, H, ha, hH, hc, hlo, hhi⟩ := exists_translated_coefficient_position hdpos f hf hf0
  let model := homogeneousTranslation ℤ a f
  have hmhom : model.IsHomogeneous d := homogeneousTranslation_homogeneous a hf
  have hm0 : model ≠ 0 := by
    exact (homogeneousTranslation ℤ a).injective.ne (by simpa using hf0)
  have hmir : Irreducible (map (Int.castRingHom K) model) := by
    dsimp only [model]
    rw [homogeneousTranslation_map]
    exact (MulEquiv.irreducible_iff
      (f := homogeneousTranslation K ((Int.castRingHom K) ∘ a))).mpr hir
  obtain ⟨hmdeg, hmchart⟩ := homogeneous_absolute_chart_data model hmhom hd hmir
  let w := fun i => homogeneousPointTranslation (-a) (z i)
  have hw0 : ∀ i, w i ≠ 0 := fun i => homogeneousPointTranslation_ne_zero (-a) (hz0 i)
  have hwi : Function.Injective (fun i => Projectivization.mk ℚ (rationalPoint (w i))
      (rationalPoint_ne_zero (hw0 i))) :=
    homogeneousPointTranslation_projective_injective (-a) z hz0 hinj
  have hwp : ∀ i, Finset.univ.gcd (w i) = 1 := by
    intro i
    exact (homogeneousPointTranslation_gcd (-a) (z i)).trans (hzprim i)
  have hwz : ∀ i, eval (w i) model = 0 := by
    intro i
    rw [homogeneousTranslation_eval]
    change eval (homogeneousPointTranslation a (homogeneousPointTranslation (-a) (z i))) f = 0
    have he := homogeneousPointTranslation_inverse (-a) (z i)
    simp only [neg_neg] at he
    rw [he, hz i]
  let R := ((d : ℝ) + 1) * B
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le
    (by have := Nat.cast_nonneg (α := ℝ) d; linarith) hB
  have hwbox : ∀ i, InBox (w i) R :=
    fun i j => homogeneousPointTranslation_box hB a ha (z i) (hbox i) j
  have hmp := hprim.translate_homogeneous a
  by_cases hsmall : Real.log H ≤ 4 * d * Real.log R
  · have ht := projective_points_small_height_bound MonomialOrder.lex model hmhom hm0 hd hmp
      ⟨hmdeg, hmchart, hH, hc⟩ w hw0 hwi ⟨⟨hR, hwz, hwbox⟩, hwp⟩ (hlo.trans hsmall)
    have hL : 0 < |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (MonomialOrder.lex.leadingCoeff_ne_zero_iff.mpr hm0))
    have hratio := scaled_positioned_height_ratio_le hdpos (h := 1) le_rfl
      (by simpa using hH) hL hhi
    simp only [Real.log_one, zero_div, add_zero, Real.one_rpow, div_one] at hratio
    have hterm := mul_le_mul_of_nonneg_left hratio (show 0 ≤
      2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) * (d : ℝ) ^ 3 *
          R ^ (2 / (d : ℝ))
      by positivity)
    have hbound : (d : ℝ) + Real.log R +
        2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) *
            (d : ℝ) ^ 3 *
          (1 + Real.log H / (d : ℝ) ^ 2) * R ^ (2 / (d : ℝ)) /
            |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) + 2 ≤
        scaledPlaneAuxiliaryDegreeBound d projectivePlaneDeterminantConstant R 1 := by
      unfold scaledPlaneAuxiliaryDegreeBound
      simp only [Real.log_one, zero_div, add_zero, mul_one, Real.one_rpow, div_one]
      ring_nf at hterm ⊢
      linarith only [hterm]
    exact (ht.trans (mul_le_mul_of_nonneg_left hbound (by positivity))).trans (le_max_left _ _)
  · have ht := projective_points_large_height_bound MonomialOrder.lex model hmhom hm0 hd hmp
      ⟨hmdeg, hmchart, hH, hc⟩ w hw0 hwi ⟨⟨hR, hwz, hwbox⟩, hwp⟩ 14 (by norm_num)
      (le_of_lt (lt_of_not_ge hsmall)) hhi
    rw [show heightDeterminantError projectivePlaneDeterminantConstant + 6 + 14 =
        heightDeterminantError projectivePlaneDeterminantConstant + 20 by ring] at ht
    exact ht.trans (le_max_right _ _)

end
end CCDN
