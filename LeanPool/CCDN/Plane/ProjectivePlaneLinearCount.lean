/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.ProjectivePlaneAbsoluteCount
import LeanPool.CCDN.Algebra.PrimitiveNormalization
import LeanPool.CCDN.ForMathlib.SchwartzZippel
import LeanPool.CCDN.Plane.ProjectivePlaneNonabsoluteCount

/-! The elementary linear case completes the uniform plane-equation
bound in every positive degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma integer_ternary_zero_box_card_le (f : MvPolynomial (Fin 3) ℤ) (hf : f ≠ 0)
    {B : ℝ} (hB : 1 ≤ B) :
    (((integerBox 3 B).filter (fun x => eval x f = 0)).card : ℝ) ≤
      f.totalDegree * (3 * B) ^ 2 := by
  classical
  let S := Finset.Icc (-⌊B⌋) ⌊B⌋
  have hfloor : 0 ≤ ⌊B⌋ := Int.floor_nonneg.mpr (by linarith)
  have hSne : S.Nonempty := ⟨0, Finset.mem_Icc.mpr ⟨by omega, hfloor⟩⟩
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  have h : ((integerBox 3 B).filter (fun x => eval x f = 0)).card * S.card ≤
      f.totalDegree * S.card ^ 3 := by
    simpa only [integerBox, S, Fintype.card_fin] using schwartz_zippel_totalDegree_card hf S
  have hcard : (((integerBox 3 B).filter (fun x => eval x f = 0)).card : ℝ) ≤
      f.totalDegree * (S.card : ℝ) ^ 2 := by
    refine le_of_mul_le_mul_right ?_ hSpos
    rw [mul_assoc, ← pow_succ]
    exact_mod_cast h
  have hScard : (S.card : ℝ) ≤ 3 * B := by
    dsimp only [S]
    rw [Int.card_Icc]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    have hh := Int.floor_le B
    linarith
  exact hcard.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hSpos.le hScard 2) (by positivity))

private theorem projective_plane_linear_count
    (f : MvPolynomial (Fin 3) ℚ) (hf : f.IsHomogeneous 1) (hf0 : f ≠ 0)
    {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤ 9 * B ^ 2 := by
  classical
  obtain ⟨g, a, _, ha, he⟩ := exists_primitive_integer_model f hf0
  have hgh := rational_scalar_model_homogeneous he hf
  have hg0 : g ≠ 0 := by
    intro h
    have hzero : C a * f = 0 := by simpa [h] using he.symm
    exact mul_ne_zero (C_eq_zero.not.mpr ha) hf0 hzero
  have hzero : projectiveZeroLocus (map (Int.castRingHom ℚ) g) = projectiveZeroLocus f := by
    ext x
    exact rational_scalar_model_zero_iff ha he x.rep
  rw [← hzero]
  apply projective_zero_count_le_of_family_bound g hgh
  intro t z hz0 hinj _ hz hbox
  let T := (integerBox 3 B).filter (fun x => eval x g = 0)
  let ψ : Fin t → T := fun i => ⟨z i, Finset.mem_filter.mpr ⟨mem_integerBox.mpr (hbox i), hz i⟩⟩
  have hψ : Function.Injective ψ := by
    intro i j heq
    have hzi : z i = z j := congrArg Subtype.val heq
    apply hinj
    apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr
    exact ⟨1, by simp [hzi]⟩
  have hc := Fintype.card_le_of_injective ψ hψ
  have hcR : (t : ℝ) ≤ T.card := by
    exact_mod_cast (show t ≤ T.card by simpa only [Fintype.card_fin, Fintype.card_coe] using hc)
  have hb := integer_ternary_zero_box_card_le g hg0 hB
  rw [hgh.totalDegree hg0] at hb
  have hh := hcR.trans hb
  convert hh using 1
  norm_num
  ring

/-- Uniform CCDN Theorem 2 for rational projective plane equations,
in every positive degree and for every real B >= 1. -/
theorem projective_plane_equation_bound {d : ℕ}
    (f : MvPolynomial (Fin 3) ℚ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible f) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
  by_cases hd1 : d = 1
  · subst d
    have h := projective_plane_linear_count f hf hir.ne_zero hB
    have hC : 9 ≤ projectivePlaneAbsoluteConstant := by
      unfold projectivePlaneAbsoluteConstant
      have hpos := Real.exp_pos
        (heightDeterminantError projectivePlaneDeterminantConstant + 20)
      have hpos' : 0 ≤
          2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) *
            Real.exp 14 * Real.exp 2 := by positivity
      linarith
    norm_num only [Nat.cast_one, one_pow, mul_one, div_one, Real.rpow_two]
    exact h.trans (mul_le_mul_of_nonneg_right hC (sq_nonneg B))
  · exact projective_plane_rational_count f hf (by omega) hir hB

end
end CCDN
