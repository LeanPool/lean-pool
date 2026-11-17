/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import LeanPool.AutoconvolutionSharpness.Definitions
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tent expansions and interpolation of step-function autoconvolution
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace Autoconvolutions

/-- A unit cell of height `v`, including its left endpoint. -/
noncomputable def cell (a v : ℝ) : ℝ → ℝ := (Ico a (a + 1)).indicator (fun _ => v)

/-- The triangular kernel supported on `[0,2]`, with peak at one. -/
noncomputable def tent (x : ℝ) : ℝ := max 0 (min x (2 - x))

private theorem cellProduct_ae (a b v w x : ℝ) :
    (fun t => cell a v t * cell b w (x - t)) =ᵐ[volume]
      (Icc (max a (x - b - 1)) (min (a + 1) (x - b))).indicator (fun _ => v * w) := by
  filter_upwards [volume.ae_ne (a + 1), volume.ae_ne (x - b - 1)] with t ht₁ ht₂
  have hiff : t ∈ Icc (max a (x - b - 1)) (min (a + 1) (x - b)) ↔
      t ∈ Ico a (a + 1) ∧ x - t ∈ Ico b (b + 1) := by
    simp only [mem_Icc, max_le_iff, le_min_iff, mem_Ico]
    constructor
    · rintro ⟨⟨h₁,h₂⟩, h₃,h₄⟩
      exact ⟨⟨h₁, lt_of_le_of_ne h₃ ht₁⟩, by linarith, by
        have := lt_of_le_of_ne h₂ (Ne.symm ht₂)
        linarith⟩
    · rintro ⟨⟨h₁,h₂⟩, h₃,h₄⟩
      exact ⟨⟨h₁, by linarith⟩, h₂.le, by linarith⟩
  classical
  by_cases ha : t ∈ Ico a (a + 1) <;> by_cases hb : x - t ∈ Ico b (b + 1) <;>
    simp [cell, Set.indicator, ha, hb, hiff]

private theorem integrable_cellProduct (a b v w x : ℝ) :
    Integrable (fun t => cell a v t * cell b w (x - t)) := by
  apply Integrable.congr _ (cellProduct_ae a b v w x).symm
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact integrableOn_const (by simp)

/-- The genuine Bochner convolution of two unit cells is their translated tent.
The two potentially exceptional endpoints of the integrand have measure zero. -/
theorem integral_cell_mul_cell (a b v w x : ℝ) :
    (∫ t, cell a v t * cell b w (x - t)) = v * w * tent (x - a - b) := by
  rw [integral_congr_ae (cellProduct_ae a b v w x), integral_indicator measurableSet_Icc,
    setIntegral_const, Real.volume_real_Icc, smul_eq_mul]
  have hlength : max (min (a + 1) (x - b) - max a (x - b - 1)) 0 = tent (x - a - b) := by
    by_cases h : x - a - b ≤ 1
    · rw [min_eq_right (by linarith : x - b ≤ a + 1),
        max_eq_left (by linarith : x - b - 1 ≤ a), tent,
        min_eq_left (by linarith : x - a - b ≤ 2 - (x - a - b))]
      rw [max_comm]
      congr 1
      ring
    · rw [min_eq_left (by linarith : a + 1 ≤ x - b),
        max_eq_right (by linarith : a ≤ x - b - 1), tent,
        min_eq_right (by linarith : 2 - (x - a - b) ≤ x - a - b)]
      rw [max_comm]
      congr 1
      ring
  rw [hlength]
  ring

/-- The coefficient of degree `k` in the square, extended by zero to negative degrees. -/
noncomputable def convCoeff (d : ℕ) (p : Fin (d + 1) → ℝ) (k : ℤ) : ℝ :=
  ∑ i, ∑ j, if (i.val : ℤ) + j.val = k then p i * p j else 0

/-- Expansion of the analytic convolution into translates of the unit tent. -/
theorem auto_step_tents (d : ℕ) (p : Fin (d + 1) → ℝ) (x : ℝ) :
    auto (step d p) x = ∑ i, ∑ j, p i * p j * tent (x - i.val - j.val) := by
  classical
  have hs (t : ℝ) : step d p t = ∑ i, cell i.val (p i) t := by
    rfl
  simp only [auto, hs, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_cellProduct i.val j.val (p i) (p j) x))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => integrable_cellProduct i.val j.val (p i) (p j) x)]
  exact Finset.sum_congr rfl (fun j _ => integral_cell_mul_cell _ _ _ _ _)

theorem continuous_auto_step (d : ℕ) (p : Fin (d + 1) → ℝ) : Continuous (auto (step d p)) := by
  simp_rw [show auto (step d p) = _ from funext (auto_step_tents d p)]
  unfold tent
  fun_prop

theorem hasCompactSupport_auto_step (d : ℕ) (p : Fin (d + 1) → ℝ) :
    HasCompactSupport (auto (step d p)) := by
  apply HasCompactSupport.intro (K := Icc 0 (2 * (d : ℝ) + 2)) isCompact_Icc
  intro x hx
  rw [auto_step_tents]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hi : (i.val : ℝ) ≤ d := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hj : (j.val : ℝ) ≤ d := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  have hi' : 0 ≤ (i.val : ℝ) := by positivity
  have hj' : 0 ≤ (j.val : ℝ) := by positivity
  have hs : tent (x - i.val - j.val) = 0 := by
    unfold tent
    apply max_eq_left
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  rw [hs, mul_zero]

private theorem tent_on_cell (m k : ℤ) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    tent ((k : ℝ) + 1 + u - (m : ℝ)) =
      (if m = k then 1 - u else 0) + (if m = k + 1 then u else 0) := by
  by_cases h₁ : m = k
  · subst m
    simp only [tent, max_def, min_def]
    split_ifs <;> first | omega | linarith
  by_cases h₂ : m = k + 1
  · subst m
    push_cast
    simp only [h₁, ite_false, ite_true, zero_add, tent, max_def, min_def]
    split_ifs <;> linarith
  simp only [h₁, h₂, ite_false, zero_add, tent]
  apply max_eq_left
  by_cases h₃ : m < k
  · have hm : (m : ℝ) + 1 ≤ k := by exact_mod_cast (show m + 1 ≤ k by omega)
    exact (min_le_right _ _).trans (by linarith)
  · have hm : (k : ℝ) + 2 ≤ m := by exact_mod_cast (show k + 2 ≤ m by omega)
    exact (min_le_left _ _).trans (by linarith)

/-- Linear interpolation on every lattice interval, including the outer zero cells. -/
theorem auto_step_interpolate (d : ℕ) (p : Fin (d + 1) → ℝ) (k : ℤ)
    (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    auto (step d p) ((k : ℝ) + 1 + u) = (1 - u) * convCoeff d p k + u * convCoeff d p (k + 1) := by
  classical
  rw [auto_step_tents]
  unfold convCoeff
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hx : (k : ℝ) + 1 + u - i.val - j.val = (k : ℝ) + 1 + u - (((i.val : ℤ) + j.val : ℤ) : ℝ) :=
      by
    push_cast
    ring
  rw [hx, tent_on_cell _ _ _ hu hu']
  split_ifs <;> ring

theorem auto_step_plateau (d : ℕ) (p : Fin (d + 1) → ℝ) (k : ℤ) (H : ℝ)
    (h₀ : convCoeff d p k = H) (h₁ : convCoeff d p (k + 1) = H) :
    ∀ x ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2), auto (step d p) x = H := by
  rintro x ⟨hxl, hxr⟩
  have hx : x = (k : ℝ) + 1 + (x - (k + 1)) := by ring
  nth_rw 1 [hx]
  rw [auto_step_interpolate _ _ _ _ (by linarith) (by linarith), h₀, h₁]
  ring

end Autoconvolutions
