/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.Exponents
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Lengths

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The radial length `ℓ_r(t) = (−t)^{1/2}` of `eq:aniso:lengths`. -/
@[expose] def radialLength (t : ℝ) : ℝ := (-t) ^ (1 / 2 : ℝ)
/-- The axial length `ℓ_z(t) = (−t)^{1/2 − h}` of `eq:aniso:lengths`. -/
@[expose] def axialLength (h t : ℝ) : ℝ := (-t) ^ (1 / 2 - h)
/-- The ratio `δ = ℓ_r/ℓ_z = (−t)^h` of `eq:aniso:zoom:lengths`. -/
@[expose] def lengthRatio (h t : ℝ) : ℝ := (-t) ^ h

theorem radialLength_rpow_two_mul {t : ℝ} (ht : t < 0) (h : ℝ) :
    radialLength t ^ (2 * h) = lengthRatio h t := by
  dsimp [radialLength, lengthRatio]
  have hpos : 0 ≤ -t := by linarith only [ht]
  calc
    ((-t) ^ (1 / 2 : ℝ)) ^ (2 * h) = (-t) ^ ((1 / 2 : ℝ) * (2 * h)) := by
      rw [Real.rpow_mul hpos]
    _ = (-t) ^ h := by
      congr 1
      ring

theorem radialLength_rpow_one_sub {t : ℝ} (ht : t < 0) (h : ℝ) :
    radialLength t ^ (1 - 2 * h) = axialLength h t := by
  dsimp [radialLength, axialLength]
  have hpos : 0 ≤ -t := by linarith only [ht]
  calc
    ((-t) ^ (1 / 2 : ℝ)) ^ (1 - 2 * h) = (-t) ^ ((1 / 2 : ℝ) * (1 - 2 * h)) := by
      rw [Real.rpow_mul hpos]
    _ = (-t) ^ (1 / 2 - h) := by
      congr 1
      ring

theorem radialLength_eq_mul {t : ℝ} (ht : t < 0) (h : ℝ) :
    radialLength t = lengthRatio h t * axialLength h t := by
  dsimp [radialLength, lengthRatio, axialLength]
  have hpos : 0 < -t := by linarith only [ht]
  calc
    (-t) ^ (1 / 2 : ℝ) = (-t) ^ (h + (1 / 2 - h)) := by
      congr 1
      ring
    _ = (-t) ^ h * (-t) ^ (1 / 2 - h) := by rw [Real.rpow_add hpos h (1 / 2 - h)]
    _ = (-t) ^ h * (-t) ^ (1 / 2 - h) := rfl

theorem radialLength_sq {t : ℝ} (ht : t < 0) : radialLength t ^ 2 = -t :=
  zoom_lambda_sq ht

theorem tendsto_radialLength : Tendsto radialLength (𝓝[<] 0) (𝓝 0) := by
  have h := tendsto_zoom_lengths (by
    constructor
    · norm_num
    · norm_num : (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < 1 / 2)
  exact h.1

theorem tendsto_lengthRatio {h : ℝ} (hh : 0 < h) : Tendsto (lengthRatio h) (𝓝[<] 0) (𝓝 0) := by
  unfold lengthRatio
  have h_cont : ContinuousAt (fun x : ℝ => x ^ h) 0 :=
    Real.continuousAt_rpow_const (x := 0) (q := h) (Or.inr (by linarith only [hh]))
  have h_zero : (0 : ℝ) ^ h = 0 := Real.zero_rpow hh.ne'
  have h_tendsto : Tendsto (fun x : ℝ => x ^ h) (𝓝 0) (𝓝 0) := by
    have := h_cont.tendsto
    rw [h_zero] at this
    exact this
  have h_neg_tendsto : Tendsto (fun t : ℝ => -t) (𝓝[<] 0) (𝓝 0) := by
    have h' : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      have := (continuous_neg (G := ℝ)).continuousAt (x := 0)
      simpa using this.tendsto
    exact h'.mono_left nhdsWithin_le_nhds
  exact h_tendsto.comp h_neg_tendsto

theorem tendsto_axialLength {h : ℝ} (hh : h < 1 / 2) : Tendsto (axialLength h) (𝓝[<] 0) (𝓝 0) := by
  unfold axialLength
  have h_exp_pos : 0 < 1 / 2 - h := by linarith only [hh]
  have h_cont : ContinuousAt (fun x : ℝ => x ^ (1 / 2 - h)) 0 :=
    Real.continuousAt_rpow_const (x := 0) (q := 1 / 2 - h) (Or.inr (by linarith only [h_exp_pos]))
  have h_zero : (0 : ℝ) ^ (1 / 2 - h) = 0 := Real.zero_rpow h_exp_pos.ne'
  have h_tendsto : Tendsto (fun x : ℝ => x ^ (1 / 2 - h)) (𝓝 0) (𝓝 0) := by
    have := h_cont.tendsto
    rw [h_zero] at this
    exact this
  have h_neg_tendsto : Tendsto (fun t : ℝ => -t) (𝓝[<] 0) (𝓝 0) := by
    have h' : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      have := (continuous_neg (G := ℝ)).continuousAt (x := 0)
      simpa using this.tendsto
    exact h'.mono_left nhdsWithin_le_nhds
  exact h_tendsto.comp h_neg_tendsto

theorem tendsto_neg_rpow_of_pos {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => (-t) ^ a) (𝓝[<] 0) (𝓝 0) := by
  have h_cont : ContinuousAt (fun x : ℝ => x ^ a) 0 :=
    Real.continuousAt_rpow_const (x := 0) (q := a) (Or.inr (by linarith only [ha]))
  have h_zero : (0 : ℝ) ^ a = 0 := Real.zero_rpow ha.ne'
  have h_tendsto : Tendsto (fun x : ℝ => x ^ a) (𝓝 0) (𝓝 0) := by
    have := h_cont.tendsto
    rw [h_zero] at this
    exact this
  have h_neg_tendsto : Tendsto (fun t : ℝ => -t) (𝓝[<] 0) (𝓝 0) := by
    have h' : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      have := (continuous_neg (G := ℝ)).continuousAt (x := 0)
      simpa using this.tendsto
    exact h'.mono_left nhdsWithin_le_nhds
  exact h_tendsto.comp h_neg_tendsto

end CIV
