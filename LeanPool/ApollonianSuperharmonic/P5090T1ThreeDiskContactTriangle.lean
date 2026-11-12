/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Analysis.Normed.Module.Basic

-- [TABLET NODE: P5090T1ThreeDiskContactTriangle]

/-!
# P5090T1ThreeDiskContactTriangle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5090T1ThreeDiskContactTriangle (A B C z : ℂ) (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hAB : dist A B = a + b) (hAC : dist A C = a + c)
    (hBC : dist B C = b + c)
    (hz : z ∈ convexHull ℝ ({A, B, C} : Set ℂ))
    (hzA : a ≤ dist z A) (hzB : b ≤ dist z B) (hzC : c ≤ dist z C) :
    z ∈ convexHull ℝ
      ({(b / (a + b)) • A + (a / (a + b)) • B,
        (c / (a + c)) • A + (a / (a + c)) • C,
        (c / (b + c)) • B + (b / (b + c)) • C} : Set ℂ) := by
-- BODY
  have triangleWeights (A B C z : ℂ) (hz :
      z ∈ convexHull ℝ ({A, B, C} : Set ℂ)) :
      ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
        z = α • A + β • B + γ • C := by
    let T : Set ℂ := {z | ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧
      α + β + γ = 1 ∧ z = α • A + β • B + γ • C}
    have hT : Convex ℝ T := by
      intro x hx y hy u v hu hv huv
      rcases hx with ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩
      rcases hy with ⟨α', β', γ', hα', hβ', hγ', hsum', rfl⟩
      refine ⟨u * α + v * α', u * β + v * β', u * γ + v * γ', ?_, ?_, ?_, ?_, ?_⟩
      · positivity
      · positivity
      · positivity
      · calc
          (u * α + v * α') + (u * β + v * β') + (u * γ + v * γ') =
              u * (α + β + γ) + v * (α' + β' + γ') := by ring
          _ = 1 := by rw [hsum, hsum']; nlinarith
      · module
    have hsub : ({A, B, C} : Set ℂ) ⊆ T := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by module⟩
      · exact ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by module⟩
      · exact ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num, by module⟩
    have hzt : z ∈ T := (convexHull_min hsub hT) hz
    simpa only [T, Set.mem_ofPred_eq] using hzt
  have contactCombo (A B C : ℂ) (a b c α β γ : ℝ)
      (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
      (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
      (hsum : α + β + γ = 1)
      (hA : a ≤ β * (a + b) + γ * (a + c))
      (hB : b ≤ α * (a + b) + γ * (b + c))
      (hC : c ≤ α * (a + c) + β * (b + c)) :
      ∃ μD μE μF : ℝ, 0 ≤ μD ∧ 0 ≤ μE ∧ 0 ≤ μF ∧
        μD + μE + μF = 1 ∧
        α • A + β • B + γ • C =
          μD • ((b / (a + b)) • A + (a / (a + b)) • B) +
          μE • ((c / (a + c)) • A + (a / (a + c)) • C) +
          μF • ((c / (b + c)) • B + (b / (b + c)) • C) := by
    let μD := (a + b) * (α * (a + c) + β * (b + c) - c) / (2 * a * b)
    let μE := (a + c) * (α * (a + b) + γ * (b + c) - b) / (2 * a * c)
    let μF := (b + c) * (β * (a + b) + γ * (a + c) - a) / (2 * b * c)
    have hγeq : γ = 1 - α - β := by linarith [hsum]
    have hμD : 0 ≤ μD := by
      dsimp [μD]
      apply div_nonneg
      · apply mul_nonneg (by positivity)
        nlinarith [hC]
      · positivity
    have hμE : 0 ≤ μE := by
      dsimp [μE]
      apply div_nonneg
      · apply mul_nonneg (by positivity)
        nlinarith [hB]
      · positivity
    have hμF : 0 ≤ μF := by
      dsimp [μF]
      apply div_nonneg
      · apply mul_nonneg (by positivity)
        nlinarith [hA]
      · positivity
    have hsumμ : μD + μE + μF = 1 := by
      dsimp [μD, μE, μF]
      rw [hγeq]
      field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc,
        ne_of_gt (add_pos ha hb), ne_of_gt (add_pos ha hc), ne_of_gt (add_pos hb hc)]
      ring
    have hcomb :
        α • A + β • B + γ • C =
          μD • ((b / (a + b)) • A + (a / (a + b)) • B) +
          μE • ((c / (a + c)) • A + (a / (a + c)) • C) +
          μF • ((c / (b + c)) • B + (b / (b + c)) • C) := by
      have hD : μD * (b / (a + b)) + μE * (c / (a + c)) = α := by
        dsimp [μD, μE]
        rw [hγeq]
        field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc,
          ne_of_gt (add_pos ha hb), ne_of_gt (add_pos ha hc)]
        ring
      have hB : μD * (a / (a + b)) + μF * (c / (b + c)) = β := by
        dsimp [μD, μF]
        rw [hγeq]
        field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc,
          ne_of_gt (add_pos ha hb), ne_of_gt (add_pos hb hc)]
        ring
      have hC' : μE * (a / (a + c)) + μF * (b / (b + c)) = γ := by
        dsimp [μE, μF]
        rw [hγeq]
        field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc,
          ne_of_gt (add_pos ha hc), ne_of_gt (add_pos hb hc)]
        ring
      simp only [smul_add, smul_smul]
      rw [← hD, ← hB, ← hC']
      module
    exact ⟨μD, μE, μF, hμD, hμE, hμF, hsumμ, hcomb⟩
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hx⟩ := triangleWeights A B C z hz
  have bound (X Y Z x : ℂ) (α β γ : ℝ)
      (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hs : α + β + γ = 1)
      (hx : x = α • X + β • Y + γ • Z) :
      dist x X ≤ β * dist X Y + γ * dist X Z := by
    have heq : x - X = β • (Y - X) + γ • (Z - X) := by
      rw [hx]
      have hα : α = 1 - β - γ := by linarith
      rw [hα]
      module
    rw [dist_eq_norm, heq]
    calc
      ‖β • (Y - X) + γ • (Z - X)‖ ≤ ‖β • (Y - X)‖ + ‖γ • (Z - X)‖ :=
        norm_add_le _ _
      _ = β * dist X Y + γ * dist X Z := by
        simp only [Complex.real_smul, Complex.norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hβ, abs_of_nonneg hγ]
        rw [← dist_eq_norm, ← dist_eq_norm, dist_comm Y X, dist_comm Z X]
  have hA := hzA.trans (bound A B C z α β γ hβ hγ hsum hx)
  rw [hAB, hAC] at hA
  have hxB : z = β • B + α • A + γ • C := by rw [hx]; module
  have hB := hzB.trans (bound B A C z β α γ hα hγ (by linarith) hxB)
  rw [dist_comm B A, hAB, hBC] at hB
  have hxC : z = γ • C + α • A + β • B := by rw [hx]; module
  have hC := hzC.trans (bound C A B z γ α β hα hβ (by linarith) hxC)
  rw [dist_comm C A, dist_comm C B, hAC, hBC] at hC
  obtain ⟨μD, μE, μF, hμD, hμE, hμF, hμsum, hcomb⟩ :=
    contactCombo A B C a b c α β γ ha hb hc hα hβ hγ hsum hA hB hC
  apply mem_convexHull_of_exists_fintype (w := ![μD, μE, μF])
    (z := ![(b / (a + b)) • A + (a / (a + b)) • B,
      (c / (a + c)) • A + (a / (a + c)) • C,
      (c / (b + c)) • B + (b / (b + c)) • C])
  · intro i
    fin_cases i <;> assumption
  · simpa [Fin.sum_univ_succ, add_assoc] using hμsum
  · intro i
    fin_cases i <;> simp
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, add_zero]
    simpa only [add_assoc] using hcomb.symm.trans hx.symm

end ApollonianSuperharmonic

end
