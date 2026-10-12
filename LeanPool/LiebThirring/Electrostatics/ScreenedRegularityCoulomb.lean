/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import LeanPool.LiebThirring.Defs.Configuration

/-!
# Off-pole Coulomb differentiation

Inverse distance is smooth and harmonic away from its pole.
-/

public section

open InnerProductSpace Laplacian Filter
open scoped RealInnerProductSpace Topology

namespace LiebThirring

theorem contDiffAt_inv_nuclear_distance (y x : Position) (hx : x ≠ y)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n (fun z : Position => ‖z - y‖⁻¹) x :=
  ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hx)).inv
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))

theorem norm_sq_rpow_neg_half (x : Position) :
    (‖x‖ ^ 2) ^ (-(1 / 2 : ℝ)) = ‖x‖⁻¹ := by
  rw [Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

theorem fderiv_nuclear_distance_sq_rpow (y x v : Position) (hx : x ≠ y) (p : ℝ) :
    fderiv ℝ (fun z : Position => (‖z - y‖ ^ 2) ^ p) x v =
      2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * ⟪x - y, v⟫ := by
  have hs := ((hasFDerivAt_id x).sub_const y).norm_sq
  simp only [id_eq] at hs
  have hh := hs.rpow_const (p := p)
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))))
  rw [hh.fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply]
  ring

theorem hessian_nuclear_distance_sq_rpow (y x v : Position) (hx : x ≠ y) (p : ℝ) :
    fderiv ℝ (fderiv ℝ (fun z : Position => (‖z - y‖ ^ 2) ^ p)) x v v =
      4 * p * (p - 1) * (‖x - y‖ ^ 2) ^ (p - 2) * ⟪x - y, v⟫ ^ 2 +
        2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * ⟪v, v⟫ := by
  have hn : ‖x - y‖ ^ 2 ≠ 0 := pow_ne_zero 2
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))
  have hc : ContDiffAt ℝ 2 (fun z : Position => (‖z - y‖ ^ 2) ^ p) x :=
    ((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ).rpow_const_of_ne hn
  have hd := (hc.fderiv_right (by norm_num)).differentiableAt one_ne_zero
  have heval : fderiv ℝ (fun z => fderiv ℝ
      (fun w : Position => (‖w - y‖ ^ 2) ^ p) z v) x v =
      fderiv ℝ (fderiv ℝ (fun z : Position => (‖z - y‖ ^ 2) ^ p)) x v v := by
    rw [fderiv_clm_apply hd (differentiableAt_const v), (hasFDerivAt_const v x).fderiv]
    simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  rw [← heval]
  have he : (fun z : Position => fderiv ℝ
      (fun w : Position => (‖w - y‖ ^ 2) ^ p) z v) =ᶠ[𝓝 x]
      (fun z => 2 * p * (‖z - y‖ ^ 2) ^ (p - 1) * ⟪z - y, v⟫) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with z hz
    exact fderiv_nuclear_distance_sq_rpow y z v hz p
  rw [he.fderiv_eq]
  have hs := ((hasFDerivAt_id x).sub_const y).norm_sq
  simp only [id_eq] at hs
  have hp := (hs.rpow_const (p := p - 1) (Or.inl hn)).const_mul (2 * p)
  have hl : HasFDerivAt (fun z : Position => ⟪z - y, v⟫) (innerSL ℝ v) x := by
    simpa only [coe_innerSL_apply, inner_sub_left, real_inner_comm] using
      ((innerSL ℝ v).hasFDerivAt.sub_const ⟪y, v⟫)
  rw [(hp.fun_mul hl).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply]
  rw [show p - 1 - 1 = p - 2 by ring, real_inner_comm v (x - y)]
  ring

theorem fderiv_inv_nuclear_distance (y x v : Position) (hx : x ≠ y) :
    fderiv ℝ (fun z : Position => ‖z - y‖⁻¹) x v =
      -⟪x - y, v⟫ / ‖x - y‖ ^ 3 := by
  have he : (fun z : Position => ‖z - y‖⁻¹) =
      (fun z => (‖z - y‖ ^ 2) ^ (-(1 / 2 : ℝ))) :=
    funext (fun z => (norm_sq_rpow_neg_half (z - y)).symm)
  rw [he, fderiv_nuclear_distance_sq_rpow y x v hx]
  have hp : (‖x - y‖ ^ 2) ^ (-(1 / 2 : ℝ) - 1) = (‖x - y‖ ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast ‖x - y‖ 2, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [hp]
  ring

theorem laplacian_inv_nuclear_distance (y x : Position) (hx : x ≠ y) :
    Δ (fun z : Position => ‖z - y‖⁻¹) x = 0 := by
  have he : (fun z : Position => ‖z - y‖⁻¹) =
      (fun z => (‖z - y‖ ^ 2) ^ (-(1 / 2 : ℝ))) :=
    funext (fun z => (norm_sq_rpow_neg_half (z - y)).symm)
  rw [he, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [hessian_nuclear_distance_sq_rpow y _ _ hx, real_inner_self_eq_norm_sq,
    OrthonormalBasis.norm_eq_one, one_pow, mul_one]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    (stdOrthonormalBasis ℝ Position).sum_sq_inner_left]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdim : Module.finrank ℝ Position = 3 := by
    simp only [Position, finrank_euclideanSpace_fin]
  rw [hdim]
  have hp : (‖x - y‖ ^ 2) ^ (-(1 / 2 : ℝ) - 1) =
      (‖x - y‖ ^ 2) * (‖x - y‖ ^ 2) ^ (-(1 / 2 : ℝ) - 2) := by
    calc
      _ = (‖x - y‖ ^ 2) ^ (1 + (-(1 / 2 : ℝ) - 2)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add (sq_pos_of_pos
        (norm_pos_iff.mpr (sub_ne_zero.mpr hx))), Real.rpow_one]
  rw [hp]
  ring

end LiebThirring

end
