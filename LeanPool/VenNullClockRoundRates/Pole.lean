/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt module imports and source presentation. -/

module
public import LeanPool.VenNullClockRoundRates.Filter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Quantitative lower bound on a signed, pole-localized moment. -/
@[expose] public section
noncomputable section
open MeasureTheory VenMask
namespace VenRate

theorem pole_integral {μ : Measure UnitSphere} [IsFiniteMeasure μ]
    {U W : UnitSphere → ℝ} {h δ g K : ℝ} (hi : Integrable U μ) (hw : Integrable W μ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hd : 0 < δ) (hd1 : δ ≤ 1) (hg : 0 ≤ g) (hK : 0 ≤ K)
    (hbound : ∀ᵐ y ∂μ, 0 ≤ W y ∧ -(K * W y) ≤ U y ∧ (firstEnergy y ≤ δ → g ≤ U y))
    (k : ℕ) :
    μ.real {y | firstEnergy y < δ / 4} * (g * (1 - δ / 4) ^ k) -
      (K * (1 - δ / 2) ^ k) * (∫ y, W y ∂μ) ≤ filtered μ U h k 0 := by
  classical
  let s := {y | firstEnergy y < δ / 4}
  have hs : MeasurableSet s := (isOpen_lt first_cont continuous_const).measurableSet
  let S := g * (1 - δ / 4) ^ k
  let B := K * (1 - δ / 2) ^ k
  have B0 : 0 ≤ B := mul_nonneg hK (pow_nonneg (by linarith) _)
  have intI : Integrable (s.indicator (fun _ : UnitSphere ↦ S)) μ :=
    (integrable_const _).indicator hs
  have intP : Integrable (fun y ↦ U y * poleFilter h (firstEnergy y) ^ k) μ := by
    simpa using filtered_integrable hi hh hh1 k 0
  have L := integral_mono_ae (intI.sub (hw.const_mul B)) intP (by
    filter_upwards [hbound] with y hY
    simp only [Pi.sub_apply]
    change s.indicator (fun _ ↦ S) y - B * W y ≤ U y * poleFilter h (firstEnergy y) ^ k
    let p := poleFilter h (firstEnergy y)
    obtain ⟨l, u⟩ := filter_bounds hh hh1 (en_bounds 0 y).1
    have hp : 0 ≤ p := by dsimp [p]; linarith [(en_bounds 0 y).1.2]
    have hp' : 0 ≤ p ^ k := pow_nonneg hp k
    have db := mul_nonneg B0 hY.1
    by_cases hys : y ∈ s
    · rw [Set.indicator_of_mem hys]
      change firstEnergy y < δ / 4 at hys
      have hl : 1 - δ / 4 ≤ p := by dsimp [p]; linarith
      have h₁ := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - δ / 4) hl k
      have h₂ := mul_le_mul_of_nonneg_right (hY.2.2 (by linarith)) hp'
      have h₃ := mul_le_mul_of_nonneg_left h₁ hg
      change S - B * W y ≤ U y * p ^ k
      dsimp only [S]; linarith
    · rw [Set.indicator_of_notMem hys]
      by_cases hδ : firstEnergy y ≤ δ
      · have hpos := mul_nonneg (hg.trans (hY.2.2 hδ)) hp'
        change 0 - B * W y ≤ U y * p ^ k; linarith
      · have hpR : p ≤ 1 - δ / 2 := by dsimp [p]; linarith
        have h₁ := pow_le_pow_left₀ hp hpR k
        have h₂ := mul_le_mul_of_nonneg_left h₁ (mul_nonneg hK hY.1)
        have h₃ := mul_le_mul_of_nonneg_right hY.2.1 hp'
        change 0 - B * W y ≤ U y * p ^ k
        dsimp only [B]; linarith only [h₂, h₃])
  simp only [Pi.sub_apply] at L
  rw [integral_sub intI (hw.const_mul B), integral_indicator_const _ hs, integral_const_mul] at L
  simpa [s, S, B, filtered] using L
end VenRate
end
