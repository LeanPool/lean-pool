/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Compactness Approx

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace CKN.Leray

/-- Uniform convergence of measurable scalar fields on a finite product
measure space implies convergence of their integrated squared errors. This
is the estimate used for each fixed finite-rank spatial approximation. -/
theorem tendsto_lintegral_prod_sq_of_uniform
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {E : Type*} [NormedAddCommGroup E] [ContinuousENorm E]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : ℕ → α × β → E} {g : α × β → E}
    (hconv : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop,
      ∀ z, ‖f n z - g z‖ₑ ≤ ε) :
    Tendsto (fun n => ∫⁻ z, ‖f n z - g z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν))
      atTop (nhds 0) := by
  let V : ℝ≥0∞ := (μ.prod ν) Set.univ
  have hV : V < ⊤ := by
    dsimp [V]
    exact lt_top_iff_ne_top.mpr (measure_ne_top (μ.prod ν) Set.univ)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  let δ : ℝ≥0∞ := min 1 (ε / (V + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min one_pos (ENNReal.div_pos hε.ne'
      (ENNReal.add_ne_top.mpr ⟨hV.ne, by simp⟩))
  have hδone : δ ≤ 1 := by dsimp [δ]; exact min_le_left _ _
  have hsmall : δ ^ (2 : ℝ) * V ≤ ε := by
    calc
      δ ^ (2 : ℝ) * V ≤ δ * V := by
        apply mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc
          δ ^ (2 : ℝ) = δ * δ := by
            rw [ENNReal.rpow_two]
            exact pow_two δ
          _ ≤ δ := mul_le_of_le_one_left (by positivity) hδone
      _ ≤ ε := by
        calc
          δ * V ≤ (ε / (V + 1)) * V :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
          _ ≤ (ε / (V + 1)) * (V + 1) := by gcongr; exact le_add_right le_rfl
          _ = ε := ENNReal.div_mul_cancel (by simp) (by simp [hV.ne])
  have hevent : ∀ᶠ n in atTop, ∀ z, ‖f n z - g z‖ₑ ≤ δ := hconv δ hδ
  filter_upwards [hevent] with n hn
  have hpoint : ∀ z, ‖f n z - g z‖ₑ ^ (2 : ℝ) ≤ δ ^ (2 : ℝ) := by
    intro z
    gcongr
    exact hn z
  calc
    (∫⁻ z, ‖f n z - g z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν)) ≤
        ∫⁻ _z, δ ^ (2 : ℝ) ∂(μ.prod ν) := lintegral_mono hpoint
    _ = δ ^ (2 : ℝ) * V := by simp [V]
    _ ≤ ε := hsmall

end CKN.Leray
