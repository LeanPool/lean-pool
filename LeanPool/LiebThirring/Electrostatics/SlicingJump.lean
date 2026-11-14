/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityCells
public import LeanPool.LiebThirring.Electrostatics.FaceMeasureDirected
import all LeanPool.LiebThirring.Electrostatics.FaceMeasureBasic
import all LeanPool.LiebThirring.Electrostatics.FaceMeasureGeometry

/-!
# The derivative jump between adjacent screened representatives

The jump of directional derivatives across a genuine Voronoi face.
-/

public section

open InnerProductSpace
open scoped RealInnerProductSpace NNReal

namespace LiebThirring

theorem screenedCellPotential_sub {M : ℕ} (Z : ℝ≥0) (R : Fin M → Position)
    (k l : Fin M) (x : Position) :
    screenedCellPotential Z R l x - screenedCellPotential Z R k x =
      (Z : ℝ) * ‖x - R k‖⁻¹ - (Z : ℝ) * ‖x - R l‖⁻¹ := by
  classical
  have hk := Finset.sum_erase_add (Finset.univ : Finset (Fin M))
    (fun p => (Z : ℝ) * ‖x - R p‖⁻¹) (Finset.mem_univ k)
  have hl := Finset.sum_erase_add (Finset.univ : Finset (Fin M))
    (fun p => (Z : ℝ) * ‖x - R p‖⁻¹) (Finset.mem_univ l)
  unfold screenedCellPotential
  linear_combination hl - hk

theorem fderiv_screenedCellPotential_jump {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k l : Fin M)
    {x : Position} (hx : x ∈ voronoiFace R k l) (v : Position) :
    fderiv ℝ (screenedCellPotential Z R l) x v -
      fderiv ℝ (screenedCellPotential Z R k) x v =
        -(Z : ℝ) * ‖R l - R k‖ / ‖x - R k‖ ^ 3 * ⟪bisectorNormal R k l, v⟫ := by
  have hkl : k ≠ l := hx.1
  have hcellk := voronoiFace_subset_closed R k l hx
  have hcelll := voronoiFace_subset_closed R l k ((voronoiFace_comm R k l) ▸ hx)
  have hxk : x ≠ R k := ne_nucleus_of_mem_closedVoronoiCell R hR l k hkl hcelll
  have hxl : x ≠ R l := ne_nucleus_of_mem_closedVoronoiCell R hR k l hkl.symm hcellk
  have hcK := (contDiffAt_screenedCellPotential Z R hR k hcellk 1).differentiableAt one_ne_zero
  have hcL := (contDiffAt_screenedCellPotential Z R hR l hcelll 1).differentiableAt one_ne_zero
  have hdK := (contDiffAt_inv_nuclear_distance (R k) x hxk 1).differentiableAt one_ne_zero
  have hdL := (contDiffAt_inv_nuclear_distance (R l) x hxl 1).differentiableAt one_ne_zero
  have he : (fun y => screenedCellPotential Z R l y - screenedCellPotential Z R k y) =
      (fun y => (Z : ℝ) * ‖y - R k‖⁻¹ - (Z : ℝ) * ‖y - R l‖⁻¹) :=
    funext (screenedCellPotential_sub Z R k l)
  have hh := congrArg (fun f : Position → ℝ => fderiv ℝ f x v) he
  rw [fderiv_fun_sub hcL hcK,
    fderiv_fun_sub (hdK.const_mul _) (hdL.const_mul _),
    fderiv_const_mul hdK, fderiv_const_mul hdL] at hh
  simp only [sub_apply, smul_apply, smul_eq_mul] at hh
  rw [fderiv_inv_nuclear_distance _ _ _ hxk, fderiv_inv_nuclear_distance _ _ _ hxl] at hh
  have hr : ‖x - R k‖ = ‖x - R l‖ := by
    simpa only [dist_eq_norm] using (mem_bisectorPlane R k l x).mp hx.2.1
  rw [← hr] at hh
  rw [hh]
  have hdist : ‖R l - R k‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hR.ne hkl.symm))
  simp only [bisectorNormal, real_inner_smul_left, inner_sub_left]
  field_simp
  ring

end LiebThirring

end
