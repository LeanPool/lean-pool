/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Sobolev Six

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory
open CKN.Foundation.Parabolic CKN
open scoped ENNReal NNReal
open Module

noncomputable section

namespace CIV

/-- The Sobolev inequality in `ℝ³` for compactly supported `C¹` functions:
`L⁶` norm bounded by `L²` norm of the derivative, with an explicit constant.

We use `eLpNorm` (the `Lᵖ` norm in the sense of extended nonnegative reals) because
converting to explicit real-valued integrals would require additional measure-theoretic
identifications. -/
theorem exists_sobolev_six_const :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Vec3 → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm g 6 ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ g) 2 := by
  have h_finrank : finrank ℝ Vec3 = 3 := by
    simp [Vec3]
  have h_finrank_pos : 0 < finrank ℝ Vec3 := by
    rw [h_finrank]
    norm_num
  have hp : (1 : ℝ≥0) ≤ 2 := by norm_num
  have hp'_eq : ((6 : ℝ≥0) : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - ((finrank ℝ Vec3 : ℝ))⁻¹ := by
    rw [h_finrank]
    norm_num
  let const : ℝ≥0 := SNormLESNormFDerivOfEqConst ℝ (volume : Measure Vec3) 2
  set C : ℝ := max 1 (const : ℝ) with hC_def
  have hC_pos : 0 < C := by
    rw [hC_def]
    exact lt_max_of_lt_left (by norm_num : (0 : ℝ) < 1)
  refine ⟨C, hC_pos, ?_⟩
  intro g hg_cont hg_support
  have h_ineq := eLpNorm_le_eLpNorm_fderiv_of_eq (μ := volume) hg_cont hg_support hp
    h_finrank_pos hp'_eq
  have h_const_le : (const : ℝ≥0∞) ≤ ENNReal.ofReal C := by
    rw [hC_def]
    have hle : (const : ℝ) ≤ max 1 (const : ℝ) := le_max_right _ _
    calc
      (const : ℝ≥0∞) = ENNReal.ofReal (const : ℝ) := by simp
      _ ≤ ENNReal.ofReal (max 1 (const : ℝ)) := ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal C := by rw [hC_def]
  have h1 : eLpNorm g 6 ≤ (const : ℝ≥0∞) * eLpNorm (fderiv ℝ g) 2 := by
    simpa [const] using h_ineq
  have h2 : (const : ℝ≥0∞) * eLpNorm (fderiv ℝ g) 2 ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ g) 2 :=
    mul_le_mul_of_nonneg_right h_const_le (by simp)
  exact le_trans h1 h2

/-- Vector-field version of the Sobolev inequality in `ℝ³`.  Applied componentwise
to `v : Vec3 → Vec3` with each component `C¹` and compactly supported. -/
theorem exists_sobolev_six_const_vec :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Vec3 → Vec3), (∀ i, ContDiff ℝ 1 (fun x => v x i)) →
      (∀ i, HasCompactSupport (fun x => v x i)) →
      (∑ i, eLpNorm (μ := volume) (fun x => v x i) 6) ≤ ENNReal.ofReal C * (∑ i, eLpNorm (μ :=
        volume) (fderiv ℝ (fun x => v x i)) 2) := by
  rcases exists_sobolev_six_const with ⟨C, hC_pos, hC⟩
  refine ⟨C, hC_pos, ?_⟩
  intro v hv_cont hv_support
  have h := calc
    (∑ i, eLpNorm (μ := volume) (fun x => v x i) 6)
        ≤ (∑ i, ENNReal.ofReal C * eLpNorm (μ := volume) (fderiv ℝ (fun x => v x i)) 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact hC (fun x => v x i) (hv_cont i) (hv_support i)
    _ = ENNReal.ofReal C * (∑ i, eLpNorm (μ := volume) (fderiv ℝ (fun x => v x i)) 2) := by
      rw [Finset.mul_sum]
  exact h

end CIV
