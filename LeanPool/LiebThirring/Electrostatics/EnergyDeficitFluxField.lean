/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitFluxCutoff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# The inverse-square field and its divergence

The gradient of the inverse-square potential, with its scalar factor written by squared norm.

The inverse-square potential has precisely the displayed gradient field.
-/

@[expose] public section

open scoped ContDiff

namespace LiebThirring

/-- The gradient of the inverse-square potential, with its scalar factor written by squared norm. -/
noncomputable def exteriorInverseSquareField (c x : Position) : Position :=
  (-2 * ((‖x - c‖ ^ 2)⁻¹) ^ 2) • (x - c)

/-- Coordinate trace of the derivative on physical Euclidean space. -/
noncomputable def positionDivergence (V : Position → Position) (x : Position) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ V x (EuclideanSpace.basisFun (Fin 3) ℝ i)) i

/-- Directional derivative of the scalar factor away from the nucleus. -/
theorem hasFDerivAt_inverse_fourth_factor (c x : Position) (hx : x ≠ c) :
    HasFDerivAt (fun y : Position => -2 * ((‖y - c‖ ^ 2)⁻¹) ^ 2)
      ((8 / ‖x - c‖ ^ 6) • innerSL ℝ (x - c)) x := by
  have hn : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hs : ‖x - c‖ ^ 2 ≠ 0 := pow_ne_zero _ hn
  have hd := (hasFDerivAt_id x).sub_const c |>.norm_sq
  have hi := (hasDerivAt_inv hs).comp_hasFDerivAt x hd
  convert (hi.pow 2).const_mul (-2) using 1
  · funext y
    simp only [Function.comp_def, id_eq]
  · ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_def, id_eq,
      Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
    field_simp [hn]
    ring

/-- The vector field derivative evaluated in an arbitrary direction. -/
theorem fderiv_exteriorInverseSquareField_apply (c x v : Position) (hx : x ≠ c) :
    fderiv ℝ (exteriorInverseSquareField c) x v =
      (-2 / ‖x - c‖ ^ 4) • v +
        (8 / ‖x - c‖ ^ 6 * inner ℝ (x - c) v) • (x - c) := by
  have hd := (hasFDerivAt_inverse_fourth_factor c x hx).smul
    ((hasFDerivAt_id x).sub_const c)
  change fderiv ℝ ((fun y : Position => -2 * ((‖y - c‖ ^ 2)⁻¹) ^ 2) •
    (fun y : Position => y - c)) x v = _
  simp only [id_eq] at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_eq_mul]
  congr 2
  simp only [div_eq_mul_inv, inv_pow, ← pow_mul]

/-- Exact divergence of the inverse-square gradient off the nucleus. -/
theorem positionDivergence_exteriorInverseSquareField (c x : Position) (hx : x ≠ c) :
    positionDivergence (exteriorInverseSquareField c) x = 2 / ‖x - c‖ ^ 4 := by
  unfold positionDivergence
  simp_rw [fderiv_exteriorInverseSquareField_apply c x _ hx,
    EuclideanSpace.inner_basisFun_real]
  have he (i : Fin 3) :
      ((-2 / ‖x - c‖ ^ 4) • EuclideanSpace.basisFun (Fin 3) ℝ i +
        (8 / ‖x - c‖ ^ 6 * (x - c) i) • (x - c)) i =
      -2 / ‖x - c‖ ^ 4 + 8 / ‖x - c‖ ^ 6 * ((x - c) i) ^ 2 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.basisFun_apply,
      PiLp.single_apply, ite_true, mul_one]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  have hn : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  field_simp
  ring

/-- Applying the derivative of the scaled cutoff in the radial direction. -/
theorem fderiv_exteriorFluxCutoff_radial (c x : Position) (T : ℝ) :
    fderiv ℝ (exteriorFluxCutoff c T) x (x - c) =
      exteriorFluxDefect (T⁻¹ • (x - c)) := by
  have hs := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).fun_const_smul T⁻¹
  have hb := (exteriorFluxBump.contDiff.differentiable (by simp : (∞ : ℕ∞ω) ≠ 0)
    (T⁻¹ • (x - c))).hasFDerivAt
  have hd := hb.comp x hs
  simp only [id_eq] at hd
  rw [show fderiv ℝ (exteriorFluxCutoff c T) x =
    (fderiv ℝ (exteriorFluxBump : Position → ℝ) (T⁻¹ • (x - c))).comp
      (T⁻¹ • ContinuousLinearMap.id ℝ Position) from hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    exteriorFluxDefect]

/-- Trace of a rank-one map in the standard orthonormal frame. -/
theorem sum_position_rankOne (L : Position →L[ℝ] ℝ) (v : Position) :
    (∑ i : Fin 3, L (EuclideanSpace.basisFun (Fin 3) ℝ i) * v i) = L v := by
  calc
    _ = ∑ i : Fin 3, L (v i • EuclideanSpace.basisFun (Fin 3) ℝ i) := by
      simp only [map_smul, smul_eq_mul, mul_comm]
    _ = L (∑ i : Fin 3, v i • EuclideanSpace.basisFun (Fin 3) ℝ i) := (map_sum _ _ _).symm
    _ = L v := by
      have he := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
      simpa only [EuclideanSpace.basisFun_repr] using congrArg L he

/-- Divergence product rule for a scalar and a vector field at a differentiability point. -/
theorem positionDivergence_smul (f : Position → ℝ) (V : Position → Position) (x : Position)
    (hf : DifferentiableAt ℝ f x) (hV : DifferentiableAt ℝ V x) :
    positionDivergence (fun y => f y • V y) x =
      f x * positionDivergence V x + fderiv ℝ f x (V x) := by
  have hd := hf.hasFDerivAt.fun_smul hV.hasFDerivAt
  unfold positionDivergence
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_position_rankOne]

/-- The exact pointwise cutoff divergence, including its gradient error. -/
theorem positionDivergence_cutoff_field (c x : Position) (T : ℝ) (hx : x ≠ c) :
    positionDivergence (fun y => exteriorFluxCutoff c T y • exteriorInverseSquareField c y) x =
      exteriorFluxCutoff c T x * (2 / ‖x - c‖ ^ 4) -
        exteriorFluxDefect (T⁻¹ • (x - c)) * (2 / ‖x - c‖ ^ 4) := by
  have hV : DifferentiableAt ℝ (exteriorInverseSquareField c) x := by
    convert ((hasFDerivAt_inverse_fourth_factor c x hx).fun_smul
      ((hasFDerivAt_id x).sub_const c)).differentiableAt using 1
    funext y
    rfl
  rw [positionDivergence_smul (exteriorFluxCutoff c T) (exteriorInverseSquareField c) x
    ((contDiff_exteriorFluxCutoff c T).differentiable (by simp : (∞ : ℕ∞ω) ≠ 0) x) hV,
    positionDivergence_exteriorInverseSquareField c x hx]
  simp only [exteriorInverseSquareField, map_smul, smul_eq_mul, fderiv_exteriorFluxCutoff_radial]
  simp only [div_eq_mul_inv, inv_pow, ← pow_mul]
  ring

end LiebThirring

end
