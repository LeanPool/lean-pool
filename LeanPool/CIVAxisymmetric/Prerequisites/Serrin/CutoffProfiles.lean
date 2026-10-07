/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Serrin-style cutoff profiles for the interior estimates

Smooth radial and temporal cutoff functions used in the backward parabolic
windows `B(x, ρ) × [s - ρ², s]` that appear in the proof of
`lem:aniso:annulus`.  Each profile is a smooth monotone function that
transitions from 0 to 1 over a controlled interval and is identically
constant outside it.
-/

public section

open CKN.Foundation.Parabolic

noncomputable section



namespace CIV

/-- Radial profile, equal to one on `r ≤ 1/4` and to zero on `r ≥ 1`. -/
@[expose] def serrinSpaceBump (r : ℝ) : ℝ := Real.smoothTransition (4 * (1 - r) / 3)

/-- Time profile, equal to zero on `τ ≤ -1` and to one on `τ ≥ -1/2`. -/
@[expose] def serrinTimeBump (τ : ℝ) : ℝ := Real.smoothTransition (2 * τ + 2)

/-- Ball cutoff at `x` of radius `ρ` for the Euclidean norm. -/
@[expose] def serrinBallCutoff (x : Vec3) (ρ : ℝ) (y : Vec3) : ℝ :=
  serrinSpaceBump ((∑ i, (y i - x i) ^ 2) / ρ ^ 2)

theorem serrinBallCutoff_mem_Icc (x : Vec3) (ρ : ℝ) (y : Vec3) :
    serrinBallCutoff x ρ y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold serrinBallCutoff serrinSpaceBump
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem serrinBallCutoff_support (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (y : Vec3) :
    (vec3EuclideanNorm (y - x) ≤ ρ / 2 → serrinBallCutoff x ρ y = 1) ∧
      (ρ ≤ vec3EuclideanNorm (y - x) → serrinBallCutoff x ρ y = 0) ∧
      ContDiff ℝ (⊤ : ℕ∞) (serrinBallCutoff x ρ) := by
  have hsum_sq_eq : vec3EuclideanNorm (y - x) ^ 2 = ∑ i, (y i - x i) ^ 2 := by
    unfold vec3EuclideanNorm
    have hnonneg : 0 ≤ ∑ i : Fin 3, ((y - x) i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [Real.sq_sqrt hnonneg]
    simp [Pi.sub_apply]
  have hρsq_pos : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have h_contDiff : ContDiff ℝ (⊤ : ℕ∞) (serrinBallCutoff x ρ) := by
    unfold serrinBallCutoff serrinSpaceBump
    fun_prop
  refine ⟨?_, ?_, h_contDiff⟩
  · intro hle
    unfold serrinBallCutoff serrinSpaceBump
    have hnorm_sq_le : vec3EuclideanNorm (y - x) ^ 2 ≤ (ρ / 2) ^ 2 :=
      pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) hle 2
    rw [hsum_sq_eq] at hnorm_sq_le
    have hdiv : (∑ i, (y i - x i) ^ 2) / ρ ^ 2 ≤ 1 / 4 := by
      have hsq : (ρ / 2) ^ 2 = ρ ^ 2 / 4 := by ring
      rw [hsq] at hnorm_sq_le
      field_simp [hρ.ne']
      nlinarith only [hnorm_sq_le]
    have harg : 1 ≤ 4 * (1 - (∑ i, (y i - x i) ^ 2) / ρ ^ 2) / 3 := by
      nlinarith only [hdiv]
    exact Real.smoothTransition.one_of_one_le harg
  · intro hle
    unfold serrinBallCutoff serrinSpaceBump
    have hnorm_sq_ge : ρ ^ 2 ≤ vec3EuclideanNorm (y - x) ^ 2 :=
      pow_le_pow_left₀ hρ.le hle 2
    rw [hsum_sq_eq] at hnorm_sq_ge
    have hdiv : 1 ≤ (∑ i, (y i - x i) ^ 2) / ρ ^ 2 :=
      (one_le_div hρsq_pos).mpr hnorm_sq_ge
    have harg : 4 * (1 - (∑ i, (y i - x i) ^ 2) / ρ ^ 2) / 3 ≤ 0 := by
      nlinarith only [hdiv]
    exact Real.smoothTransition.zero_of_nonpos harg

theorem serrinTimeBump_support {s ρ : ℝ} (hρ : 0 < ρ) (s' : ℝ) :
    (s - ρ ^ 2 / 2 ≤ s' → serrinTimeBump ((s' - s) / ρ ^ 2) = 1) ∧
      (s' ≤ s - ρ ^ 2 → serrinTimeBump ((s' - s) / ρ ^ 2) = 0) ∧
      ContDiff ℝ (⊤ : ℕ∞) serrinTimeBump := by
  have hρsq_pos : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have h_contDiff : ContDiff ℝ (⊤ : ℕ∞) serrinTimeBump := by
    unfold serrinTimeBump
    fun_prop
  refine ⟨?_, ?_, h_contDiff⟩
  · intro hle
    unfold serrinTimeBump
    have hτ : -1 / 2 ≤ (s' - s) / ρ ^ 2 :=
      (le_div_iff₀ hρsq_pos).mpr (by nlinarith only [hle])
    have harg : 1 ≤ 2 * ((s' - s) / ρ ^ 2) + 2 := by
      nlinarith only [hτ]
    exact Real.smoothTransition.one_of_one_le harg
  · intro hle
    unfold serrinTimeBump
    have hτ : (s' - s) / ρ ^ 2 ≤ -1 :=
      (div_le_iff₀ hρsq_pos).mpr (by nlinarith only [hle])
    have harg : 2 * ((s' - s) / ρ ^ 2) + 2 ≤ 0 := by
      nlinarith only [hτ]
    exact Real.smoothTransition.zero_of_nonpos harg

end CIV
