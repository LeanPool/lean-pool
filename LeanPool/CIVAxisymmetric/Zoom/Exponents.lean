/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.Meridional
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Setting.RotationLemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exponent identities for the zoom-in map

These lemmas collect the algebraic identities satisfied by the rescaling exponents
that appear in `eq:aniso:zoom:fields` and `eq:aniso:zoom:finite:variables`.
-/

public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem zoom_lambda_sq {t : ℝ} (ht : t < 0) : ((-t) ^ (1 / 2 : ℝ)) ^ 2 = -t := by
  have hpos : 0 ≤ -t := by linarith only [ht]
  calc
    ((-t) ^ (1 / 2 : ℝ)) ^ 2 = ((-t) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
      norm_num [Real.rpow_natCast]
    _ = (-t) ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by rw [Real.rpow_mul hpos]
    _ = (-t) ^ (1 : ℝ) := by
      congr 1
      ring
    _ = -t := Real.rpow_one _

theorem zoom_lambda_eq_delta_mul_mu {lam h : ℝ} (hlam : 0 < lam) :
    lam = lam ^ (2 * h) * lam ^ (1 - 2 * h) := by
  calc
    lam = lam ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = lam ^ ((2 * h) + (1 - 2 * h)) := by
      congr 1
      ring
    _ = lam ^ (2 * h) * lam ^ (1 - 2 * h) := by rw [Real.rpow_add hlam]

theorem zoom_rescaled_exponent {lam h : ℝ} (hlam : 0 < lam) (a b : ℕ) (τ : ℝ) (hτ : τ < 0) :
    lam ^ (1 + a) * (lam ^ (1 - 2 * h)) ^ b *
        (lam ^ 2 * (-τ)) ^ (-(1 / 2 : ℝ) - a / 2 - (1 / 2 - h) * b) =
      (-τ) ^ (-(1 / 2 : ℝ) - a / 2 - (1 / 2 - h) * b) := by
  have hpos_tau : 0 ≤ -τ := by linarith only [hτ]
  have hlam_nonneg : 0 ≤ lam := hlam.le
  set e := -(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ) with he
  have h1 : lam ^ (1 + a) = lam ^ (1 + (a : ℝ)) := by
    rw [← Real.rpow_natCast lam (1 + a)]
    norm_num
  have h2 : (lam ^ (1 - 2 * h)) ^ b = (lam ^ (1 - 2 * h)) ^ (b : ℝ) := by
    rw [← Real.rpow_natCast (lam ^ (1 - 2 * h)) b]
  have h3 : lam ^ 2 = lam ^ (2 : ℝ) := by
    norm_num [Real.rpow_natCast]
  set X := (1 + (a : ℝ)) + (1 - 2 * h) * (b : ℝ) with hX
  have h_expand : lam ^ (1 + (a : ℝ)) * lam ^ ((1 - 2 * h) * (b : ℝ)) *
      (lam ^ (2 : ℝ) * (-τ)) ^ e =
      lam ^ (X + (2 : ℝ) * e) * (-τ) ^ e := by
    calc
      lam ^ (1 + (a : ℝ)) * lam ^ ((1 - 2 * h) * (b : ℝ)) *
          (lam ^ (2 : ℝ) * (-τ)) ^ e
          = lam ^ ((1 + (a : ℝ)) + (1 - 2 * h) * (b : ℝ)) * (lam ^ (2 : ℝ) * (-τ)) ^ e := by
        rw [Real.rpow_add hlam (1 + (a : ℝ)) ((1 - 2 * h) * (b : ℝ))]
      _ = lam ^ X * (lam ^ (2 : ℝ) * (-τ)) ^ e := by rw [hX]
      _ = lam ^ X * ((lam ^ (2 : ℝ)) ^ e * (-τ) ^ e) := by
        rw [Real.mul_rpow (by positivity) hpos_tau]
      _ = lam ^ X * (lam ^ ((2 : ℝ) * e) * (-τ) ^ e) := by
        rw [Real.rpow_mul hlam_nonneg (2 : ℝ) e]
      _ = (lam ^ X * lam ^ ((2 : ℝ) * e)) * (-τ) ^ e := by ring_nf
      _ = lam ^ (X + (2 : ℝ) * e) * (-τ) ^ e := by
        rw [← Real.rpow_add hlam X ((2 : ℝ) * e)]
  calc
    lam ^ (1 + a) * (lam ^ (1 - 2 * h)) ^ b *
        (lam ^ 2 * (-τ)) ^ e
        = lam ^ (1 + (a : ℝ)) * (lam ^ (1 - 2 * h)) ^ b *
          (lam ^ 2 * (-τ)) ^ e := by rw [h1]
    _ = lam ^ (1 + (a : ℝ)) * ((lam ^ (1 - 2 * h)) ^ (b : ℝ)) *
        (lam ^ 2 * (-τ)) ^ e := by rw [h2]
    _ = lam ^ (1 + (a : ℝ)) * (lam ^ ((1 - 2 * h) * (b : ℝ))) *
        (lam ^ 2 * (-τ)) ^ e := by
      rw [Real.rpow_mul hlam_nonneg (1 - 2 * h) (b : ℝ)]
    _ = lam ^ (1 + (a : ℝ)) * lam ^ ((1 - 2 * h) * (b : ℝ)) *
        (lam ^ (2 : ℝ) * (-τ)) ^ e := by rw [h3]
    _ = lam ^ (X + (2 : ℝ) * e) * (-τ) ^ e := h_expand
    _ = lam ^ (0 : ℝ) * (-τ) ^ e := by
      dsimp [X, e]
      ring_nf
    _ = 1 * (-τ) ^ e := by rw [Real.rpow_zero lam]
    _ = (-τ) ^ e := by simp
    _ = (-τ) ^ (-(1 / 2 : ℝ) - a / 2 - (1 / 2 - h) * b) := rfl

theorem zoom_rescaled_exponent_swirl {lam h : ℝ} (hlam : 0 < lam) (a b : ℕ) (τ : ℝ) (hτ : τ < 0) :
    lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
        (lam ^ 2 * (-τ)) ^ (-(1 / 2 : ℝ) - h - a / 2 - (1 / 2 - h) * b) =
      (-τ) ^ (-(1 / 2 : ℝ) - h - a / 2 - (1 / 2 - h) * b) := by
  have hpos_tau : 0 ≤ -τ := by linarith only [hτ]
  have hlam_nonneg : 0 ≤ lam := hlam.le
  set e := -(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ) with he
  have h1 : lam ^ (1 + a) = lam ^ (1 + (a : ℝ)) := by
    rw [← Real.rpow_natCast lam (1 + a)]
    norm_num
  have h2 : (lam ^ (1 - 2 * h)) ^ b = (lam ^ (1 - 2 * h)) ^ (b : ℝ) := by
    rw [← Real.rpow_natCast (lam ^ (1 - 2 * h)) b]
  have h3 : lam ^ 2 = lam ^ (2 : ℝ) := by
    norm_num [Real.rpow_natCast]
  set X := (1 + (a : ℝ)) + (2 * h) + (1 - 2 * h) * (b : ℝ) with hX
  have h_expand : lam ^ (1 + (a : ℝ)) * lam ^ (2 * h) * lam ^ ((1 - 2 * h) * (b : ℝ)) *
      (lam ^ (2 : ℝ) * (-τ)) ^ e =
      lam ^ (X + (2 : ℝ) * e) * (-τ) ^ e := by
    calc
      lam ^ (1 + (a : ℝ)) * lam ^ (2 * h) * lam ^ ((1 - 2 * h) * (b : ℝ)) *
          (lam ^ (2 : ℝ) * (-τ)) ^ e
          = lam ^ ((1 + (a : ℝ)) + (2 * h)) * lam ^ ((1 - 2 * h) * (b : ℝ)) *
            (lam ^ (2 : ℝ) * (-τ)) ^ e := by
        rw [Real.rpow_add hlam (1 + (a : ℝ)) (2 * h)]
      _ = lam ^ (((1 + (a : ℝ)) + (2 * h)) + (1 - 2 * h) * (b : ℝ)) *
          (lam ^ (2 : ℝ) * (-τ)) ^ e := by
        rw [Real.rpow_add hlam ((1 + (a : ℝ)) + (2 * h)) ((1 - 2 * h) * (b : ℝ))]
      _ = lam ^ X * (lam ^ (2 : ℝ) * (-τ)) ^ e := by rw [hX]
      _ = lam ^ X * ((lam ^ (2 : ℝ)) ^ e * (-τ) ^ e) := by
        rw [Real.mul_rpow (by positivity) hpos_tau]
      _ = lam ^ X * (lam ^ ((2 : ℝ) * e) * (-τ) ^ e) := by
        rw [Real.rpow_mul hlam_nonneg (2 : ℝ) e]
      _ = (lam ^ X * lam ^ ((2 : ℝ) * e)) * (-τ) ^ e := by ring_nf
      _ = lam ^ (X + (2 : ℝ) * e) * (-τ) ^ e := by
        rw [← Real.rpow_add hlam X ((2 : ℝ) * e)]
  calc
    lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
        (lam ^ 2 * (-τ)) ^ e
        = lam ^ (1 + (a : ℝ)) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
          (lam ^ 2 * (-τ)) ^ e := by rw [h1]
    _ = lam ^ (1 + (a : ℝ)) * lam ^ (2 * h) * ((lam ^ (1 - 2 * h)) ^ (b : ℝ)) *
        (lam ^ 2 * (-τ)) ^ e := by rw [h2]
    _ = lam ^ (1 + (a : ℝ)) * lam ^ (2 * h) * (lam ^ ((1 - 2 * h) * (b : ℝ))) *
        (lam ^ 2 * (-τ)) ^ e := by
      rw [Real.rpow_mul hlam_nonneg (1 - 2 * h) (b : ℝ)]
    _ = lam ^ (1 + (a : ℝ)) * lam ^ (2 * h) * lam ^ ((1 - 2 * h) * (b : ℝ)) *
        (lam ^ (2 : ℝ) * (-τ)) ^ e := by rw [h3]
    _ = lam ^ (X + (2 : ℝ) * e) * (-τ) ^ e := h_expand
    _ = lam ^ (0 : ℝ) * (-τ) ^ e := by
      dsimp [X, e]
      ring_nf
    _ = 1 * (-τ) ^ e := by rw [Real.rpow_zero lam]
    _ = (-τ) ^ e := by simp
    _ = (-τ) ^ (-(1 / 2 : ℝ) - h - a / 2 - (1 / 2 - h) * b) := rfl

theorem tendsto_zoom_lengths {h : ℝ} (hh : 0 < h ∧ h < 1 / 2) :
    Tendsto (fun t : ℝ => (-t) ^ (1 / 2 : ℝ)) (𝓝[<] 0) (𝓝 0) ∧
    Tendsto (fun t : ℝ => ((-t) ^ (1 / 2 : ℝ)) ^ (2 * h)) (𝓝[<] 0) (𝓝 0) ∧
    Tendsto (fun t : ℝ => ((-t) ^ (1 / 2 : ℝ)) ^ (1 - 2 * h)) (𝓝[<] 0) (𝓝 0) := by
  rcases hh with ⟨hhpos, hh_lt_half⟩
  have hhalf_pos : 0 < (1 / 2 : ℝ) := by norm_num
  have h2h_pos : 0 < 2 * h := by nlinarith only [hhpos]
  have hone_minus_2h_pos : 0 < 1 - 2 * h := by nlinarith only [hh_lt_half]
  have h_cont_sqrt : ContinuousAt (fun x : ℝ => x ^ (1 / 2 : ℝ)) 0 :=
    continuousAt_rpow_const (x := 0) (q := (1 / 2 : ℝ)) (Or.inr (by norm_num : 0 ≤ (1 / 2 : ℝ)))
  have h_cont_2h : ContinuousAt (fun x : ℝ => x ^ (2 * h)) 0 :=
    continuousAt_rpow_const (x := 0) (q := (2 * h)) (Or.inr (by nlinarith only [hhpos] : 0 ≤ 2 * h))
  have h_cont_one_minus_2h : ContinuousAt (fun x : ℝ => x ^ (1 - 2 * h)) 0 :=
    continuousAt_rpow_const (x := 0) (q := (1 - 2 * h))
      (Or.inr (by nlinarith only [hh_lt_half] : 0 ≤ 1 - 2 * h))
  have h_neg_tendsto : Tendsto (fun t : ℝ => -t) (𝓝[<] 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      have := (continuous_neg (G := ℝ)).continuousAt (x := 0)
      simpa using this.tendsto
    exact h.mono_left nhdsWithin_le_nhds
  have h_sqrt_cont : Tendsto (fun x : ℝ => x ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (1 / 2 : ℝ))) :=
    h_cont_sqrt.tendsto
  have h_zero_sqrt : (0 : ℝ) ^ (1 / 2 : ℝ) = 0 :=
    Real.zero_rpow (ne_of_gt hhalf_pos)
  have h_sqrt_tendsto_nhds : Tendsto (fun x : ℝ => x ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa [h_zero_sqrt] using h_sqrt_cont
  have h_tendsto_neg_sqrt : Tendsto (fun t : ℝ => (-t) ^ (1 / 2 : ℝ)) (𝓝[<] 0) (𝓝 0) :=
    h_sqrt_tendsto_nhds.comp h_neg_tendsto
  have h_comp_2h : Tendsto (fun x : ℝ => x ^ (2 * h)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (2 * h))) :=
    h_cont_2h.tendsto
  have h_zero_2h : (0 : ℝ) ^ (2 * h) = 0 :=
    Real.zero_rpow (ne_of_gt h2h_pos)
  have h_comp_2h_zero : Tendsto (fun x : ℝ => x ^ (2 * h)) (𝓝 0) (𝓝 0) := by
    simpa [h_zero_2h] using h_comp_2h
  have h_tendsto_2h : Tendsto (fun t : ℝ => ((-t) ^ (1 / 2 : ℝ)) ^ (2 * h)) (𝓝[<] 0) (𝓝 0) :=
    h_comp_2h_zero.comp h_tendsto_neg_sqrt
  have h_comp_one_minus_2h : Tendsto (fun x : ℝ => x ^ (1 - 2 * h)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (1 - 2 *
    h))) :=
    h_cont_one_minus_2h.tendsto
  have h_zero_one_minus_2h : (0 : ℝ) ^ (1 - 2 * h) = 0 :=
    Real.zero_rpow (ne_of_gt hone_minus_2h_pos)
  have h_comp_one_minus_2h_zero : Tendsto (fun x : ℝ => x ^ (1 - 2 * h)) (𝓝 0) (𝓝 0) := by
    simpa [h_zero_one_minus_2h] using h_comp_one_minus_2h
  have h_tendsto_one_minus_2h : Tendsto (fun t : ℝ => ((-t) ^ (1 / 2 : ℝ)) ^ (1 - 2 * h)) (𝓝[<]
    0) (𝓝 0) :=
    h_comp_one_minus_2h_zero.comp h_tendsto_neg_sqrt
  exact ⟨h_tendsto_neg_sqrt, h_tendsto_2h, h_tendsto_one_minus_2h⟩

end CIV
