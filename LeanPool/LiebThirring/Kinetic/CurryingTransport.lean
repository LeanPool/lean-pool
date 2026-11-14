/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# L² transport by measure and target isometries

Applying a target isometry pointwise is an isometry of L² classes.

Pointwise target transport has the prescribed a.e. representative.
-/

public section

open MeasureTheory

namespace LiebThirring

variable {α β E F : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Applying a target isometry pointwise is an isometry of L² classes. -/
@[expose] noncomputable def l2TargetEquiv (μ : Measure α) (A : E ≃ₗᵢ[ℂ] F) :
    Lp E 2 μ ≃ₗᵢ[ℂ] Lp F 2 μ where
  toFun := A.toContinuousLinearEquiv.toContinuousLinearMap.compLp
  invFun := A.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp
  left_inv f := by
    apply Lp.ext
    filter_upwards [A.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
      (A.toContinuousLinearEquiv.toContinuousLinearMap.compLp f),
      A.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f] with x hx hy
    rw [hx, hy]
    exact A.symm_apply_apply _
  right_inv f := by
    apply Lp.ext
    filter_upwards [A.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
      (A.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp f),
      A.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f] with x hx hy
    rw [hx, hy]
    exact A.apply_symm_apply _
  map_add' f h := by
    exact map_add (A.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ) f h
  map_smul' a f := by
    exact map_smul (A.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ) a f
  norm_map' f := by
    change ‖A.toContinuousLinearEquiv.toContinuousLinearMap.compLp f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def]
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable f)
    filter_upwards [A.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f] with x hx
    rw [hx]
    exact A.norm_map _

/-- Pointwise target transport has the prescribed a.e. representative. -/
theorem l2TargetEquiv_ae (μ : Measure α) (A : E ≃ₗᵢ[ℂ] F) (f : Lp E 2 μ) :
    l2TargetEquiv μ A f =ᵐ[μ] fun x => A (f x) :=
  A.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f

omit [NormedAddCommGroup F] [NormedSpace ℂ F] in
/-- Pullback by a measure-preserving measurable equivalence is an L² isometry. -/
@[expose] noncomputable def l2PullbackEquiv {μ : Measure α} {ν : Measure β}
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) : Lp E 2 ν ≃ₗᵢ[ℂ] Lp E 2 μ where
  toFun := Lp.compMeasurePreserving e he
  invFun := Lp.compMeasurePreserving e.symm (MeasurePreserving.symm e he)
  left_inv f := by
    have h := Lp.compMeasurePreserving_comp_apply f he (MeasurePreserving.symm e he)
    simp only [MeasurableEquiv.self_comp_symm, Lp.compMeasurePreserving_id_apply] at h
    exact h.symm
  right_inv f := by
    have h := Lp.compMeasurePreserving_comp_apply f (MeasurePreserving.symm e he) he
    simp only [MeasurableEquiv.symm_comp_self, Lp.compMeasurePreserving_id_apply] at h
    exact h.symm
  map_add' := map_add (Lp.compMeasurePreservingₗ ℂ e he)
  map_smul' := map_smul (Lp.compMeasurePreservingₗ ℂ e he)
  norm_map' := fun f => Lp.norm_compMeasurePreserving f he

omit [NormedAddCommGroup F] [NormedSpace ℂ F] in
/-- The measure transport is pullback on a.e. representatives. -/
theorem l2PullbackEquiv_ae {μ : Measure α} {ν : Measure β}
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (f : Lp E 2 ν) :
    l2PullbackEquiv e he f =ᵐ[μ] fun x => f (e x) :=
  Lp.coeFn_compMeasurePreserving f he

end LiebThirring

end
