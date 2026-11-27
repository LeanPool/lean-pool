/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.ComplexBallDerivativeBounds
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Actual derivative bounds under a real linear inclusion -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Metric Set
open scoped ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_real_comp_le {f : E → ℂ} (L : G →L[ℝ] E)
    (hL : ‖L‖ ≤ 1) (x : G) {M : ℝ} (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (ball (L x) 1))
    (hbound : ∀ y ∈ ball (L x) 1, ‖f y‖ ≤ M) {n : ℕ} (hn : n ≤ 4) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ 10000 * M := by
  have hx : L x ∈ ball (L x) 1 := mem_ball_self (by norm_num)
  have hc : ContDiffAt ℂ (n : ℕ∞ω) f (L x) := (hf _ hx).contDiffAt
  have hr : ContDiffAt ℝ (n : ℕ∞ω) f (L x) := hc.restrict_scalars ℝ
  have hcomp : ContDiffAt ℝ (n : ℕ∞ω) (f ∘ L) x :=
    hr.comp x L.contDiff.contDiffAt
  have hset : ContDiffOn ℝ (n : ℕ∞ω) f (ball (L x) 1) :=
    (hf.contDiffOn isOpen_ball.uniqueDiffOn).restrict_scalars ℝ
  have hopen : IsOpen (L ⁻¹' ball (L x) 1) := isOpen_ball.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hset isOpen_ball.uniqueDiffOn
    hopen.uniqueDiffOn hx (i := n) le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hopen.uniqueDiffOn hcomp hx,
    iteratedFDerivWithin_eq_iteratedFDeriv isOpen_ball.uniqueDiffOn hr hx] at he
  have hnorm : ‖iteratedFDeriv ℝ n f (L x)‖ = ‖iteratedFDeriv ℂ n f (L x)‖ := by
    rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
    exact ContinuousMultilinearMap.norm_restrictScalars _
  rw [he]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * ∏ _ : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * 1 := by
      gcongr
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg L) (fun _ _ => hL)
    _ = ‖iteratedFDeriv ℂ n f (L x)‖ := by rw [mul_one, hnorm]
    _ ≤ 10000 * M := norm_iteratedFDeriv_le_four hM hf hbound hn

end VacuumBellSeparation
