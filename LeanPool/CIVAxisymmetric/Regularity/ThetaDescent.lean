/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

/-!
# Theta Descent

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

theorem theta_descent_uniform {C₂₇ C₂₈ : ℝ} (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    {Θ : ℕ → ℝ → ℝ} {S : Set ℝ} {Tbar Lbar : ℝ}
    (hΘ : ∀ n, ∀ s ∈ S, 0 ≤ Θ n s) (hΘ0 : ∀ s ∈ S, Θ 0 s ≤ Tbar)
    (hrec : ∀ n, ∀ s ∈ S, Θ (n + 1) s ≤ (3 / 8 : ℝ) * Θ n s + iterationC₂₉ C₂₇ C₂₈ * Lbar)
    (hL : 0 ≤ Lbar) (hLsmall : iterationC₂₉ C₂₇ C₂₈ * Lbar ≤ iterationEta C₂₇ / 16) :
    ∃ N : ℕ, ∀ s ∈ S, Θ N s ≤ iterationEta C₂₇ := by
  set η := iterationEta C₂₇
  set A := iterationC₂₉ C₂₇ C₂₈ * Lbar
  have hη_pos : 0 < η := iterationEta_pos hC₂₇
  have hC₂₉_nonneg : 0 ≤ iterationC₂₉ C₂₇ C₂₈ :=
    (iterationC₂₉_pos hC₂₇ hC₂₈).le
  have hA_nonneg : 0 ≤ A := mul_nonneg hC₂₉_nonneg hL
  have hA_le : A ≤ η / 16 := hLsmall
  have h_three_eighths_nonneg : 0 ≤ (3 / 8 : ℝ) := by norm_num
  have h_three_eighths_lt_one : (3 / 8 : ℝ) < 1 := by norm_num
  have h_eight_fifths_nonneg : 0 ≤ (8 / 5 : ℝ) := by norm_num
  -- Induction: ∀ s ∈ S, Θ n s ≤ (3/8)^n * max Tbar 0 + (8/5) * A
  have h_bound : ∀ n : ℕ, ∀ s ∈ S,
      Θ n s ≤ ((3 / 8 : ℝ) ^ n) * max Tbar 0 + (8 / 5 : ℝ) * A := by
    intro n
    induction n with
    | zero =>
        intro s hs
        have h0 : Θ 0 s ≤ max Tbar 0 :=
          (hΘ0 s hs).trans (le_max_left _ _)
        calc
          Θ 0 s ≤ max Tbar 0 := h0
          _ ≤ max Tbar 0 + (8 / 5 : ℝ) * A :=
            le_add_of_nonneg_right (mul_nonneg h_eight_fifths_nonneg hA_nonneg)
          _ = ((3 / 8 : ℝ) ^ 0) * max Tbar 0 + (8 / 5 : ℝ) * A := by norm_num
    | succ n ih =>
        intro s hs
        have hrec_s := hrec n s hs
        have ih_s := ih s hs
        have h_mul : (3 / 8 : ℝ) * Θ n s ≤
            (3 / 8 : ℝ) * (((3 / 8 : ℝ) ^ n) * max Tbar 0 + (8 / 5 : ℝ) * A) :=
          mul_le_mul_of_nonneg_left ih_s h_three_eighths_nonneg
        calc
          Θ (n + 1) s ≤ (3 / 8 : ℝ) * Θ n s + A := hrec_s
          _ ≤ (3 / 8 : ℝ) * (((3 / 8 : ℝ) ^ n) * max Tbar 0 + (8 / 5 : ℝ) * A) + A := by
            linarith only [h_mul]
          _ = ((3 / 8 : ℝ) ^ (n + 1)) * max Tbar 0 + (8 / 5 : ℝ) * A := by ring
  -- Choose N such that (3/8)^N * max Tbar 0 ≤ η/2
  by_cases hS_empty : S = ∅
  · subst hS_empty
    refine ⟨0, fun s hs => ?_⟩
    exfalso; exact hs
  · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS_empty
    set M := max Tbar 0
    have hM_nonneg : 0 ≤ M := le_max_right _ _
    by_cases hM_zero : M = 0
    · -- M = 0: the geometric term vanishes; any N works
      refine ⟨0, fun s hs => ?_⟩
      have h0 : Θ 0 s ≤ M := (hΘ0 s hs).trans (le_max_left _ _)
      rw [hM_zero] at h0
      have hnonneg : 0 ≤ Θ 0 s := hΘ 0 s hs
      have hzero : Θ 0 s = 0 := by linarith only [h0, hnonneg]
      rw [hzero]
      exact hη_pos.le
    · have hM_pos : 0 < M := by
        by_contra! h
        exact hM_zero (le_antisymm h hM_nonneg)
      set ε := η / (2 * (M + 1)) with hε_def
      have hε_pos : 0 < ε := by
        rw [hε_def]
        refine div_pos hη_pos (by positivity)
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε_pos h_three_eighths_lt_one
      refine ⟨N, fun s hs => ?_⟩
      have h_bound_N := h_bound N s hs
      have h_pow_lt : ((3 / 8 : ℝ) ^ N) * M < η / 2 := by
        calc
          ((3 / 8 : ℝ) ^ N) * M < ε * M := mul_lt_mul_of_pos_right hN hM_pos
          _ = (η / (2 * (M + 1))) * M := rfl
          _ ≤ η / 2 := by
            field_simp
            nlinarith only [hM_pos]
      have h_pow : ((3 / 8 : ℝ) ^ N) * M ≤ η / 2 := h_pow_lt.le
      calc
        Θ N s ≤ ((3 / 8 : ℝ) ^ N) * M + (8 / 5 : ℝ) * A := h_bound_N
        _ ≤ η / 2 + (8 / 5 : ℝ) * A := by
          linarith only [h_pow]
        _ ≤ η / 2 + (8 / 5 : ℝ) * (η / 16) := by
          nlinarith only [hη_pos, hA_le]
        _ ≤ η := by
          nlinarith only [hη_pos]

end CIV
