/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The common positive offset in a matched two-strip lifting construction. -/

@[expose] public section
open MeasureTheory
open scoped ContDiff

namespace VenRateUpper

/-- The common profile with positive offset and opposite strip corrections. -/
noncomputable def twoStripProfile {Ω : Type*} (F chiPlus chiMinus : Ω → ℝ)
    (ρ : ℝ → ℝ) (K : ℝ) (y : Ω) : ℝ :=
  2 + chiPlus y * (K + ρ (F y)) + chiMinus y * K

theorem twoStripProfile_bounds {Ω : Type*} (F chiPlus chiMinus : Ω → ℝ)
    (ρ : ℝ → ℝ) {K Aplus Aminus : ℝ} (hK : 0 ≤ K) (hρ : ∀ t, |ρ t| ≤ K)
    (hPlus : ∀ y, chiPlus y ∈ Set.Icc (0 : ℝ) Aplus) (hMinus : ∀ y, chiMinus y ∈ Set.Icc (0 :
      ℝ) Aminus)
    (y : Ω) : twoStripProfile F chiPlus chiMinus ρ K y ∈ Set.Icc (2 : ℝ) (2 + Aplus * (2 * K) +
      Aminus * K) := by
  have H := abs_le.mp (hρ (F y))
  have hsum : 0 ≤ K + ρ (F y) := by linarith [H.1]
  have hup : K + ρ (F y) ≤ 2 * K := by linarith [H.2]
  constructor
  · unfold twoStripProfile
    linarith only [mul_nonneg (hPlus y).1 hsum, mul_nonneg (hMinus y).1 hK]
  · unfold twoStripProfile
    have hp := mul_le_mul (hPlus y).2 hup hsum ((hPlus y).1.trans (hPlus y).2)
    have hm := mul_le_mul_of_nonneg_right (hMinus y).2 hK
    linarith only [hp, hm]

theorem contDiff_twoStripProfile {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F chiPlus chiMinus : E → ℝ} {ρ : ℝ → ℝ} {K : ℝ}
    (hF : ContDiff ℝ ∞ F) (hPlus : ContDiff ℝ ∞ chiPlus) (hMinus : ContDiff ℝ ∞ chiMinus)
    (hρ : ContDiff ℝ ∞ ρ) : ContDiff ℝ ∞ (twoStripProfile F chiPlus chiMinus ρ K) := by
  exact (contDiff_const.add (hPlus.mul (contDiff_const.add (hρ.comp hF)))).add
    (hMinus.mul contDiff_const)

theorem integral_twoStripProfile {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [CompactSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {F q chiPlus chiMinus : Ω → ℝ}
    {η ρ f : ℝ → ℝ} (K : ℝ)
    (hF : Continuous F) (hq : Continuous q) (hchiPlus : Continuous chiPlus) (hchiMinus :
      Continuous chiMinus)
    (hη : Continuous η) (suppη : HasCompactSupport η)
    (hρ : Continuous ρ) (hf : Continuous f) (support : ∀ t, η t * ρ t = ρ t)
    (identityPlus : ∀ g : ℝ → ℝ, Continuous g →
      (∫ y, q y * chiPlus y * g (F y) ∂μ) = ∫ t, η t * g t)
    (identityMinus : ∀ g : ℝ → ℝ, Continuous g →
      (∫ y, q y * chiMinus y * g (F y) ∂μ) = -(∫ t, η t * g t)) :
    (∫ y, q y * twoStripProfile F chiPlus chiMinus ρ K y * f (F y) ∂μ) =
      (∫ y, q y * 2 * f (F y) ∂μ) + ∫ t, f t * ρ t := by
  let g₁ (t : ℝ) := K * f t
  let g₂ (t : ℝ) := ρ t * f t
  have hg₁ : Continuous g₁ := continuous_const.mul hf
  have hg₂ : Continuous g₂ := hρ.mul hf
  have hgg : Continuous (fun t => g₁ t + g₂ t) := hg₁.add hg₂
  let u (y : Ω) := q y * 2 * f (F y)
  let v (y : Ω) := q y * chiPlus y * (g₁ (F y) + g₂ (F y))
  let z (y : Ω) := q y * chiMinus y * g₁ (F y)
  have integ (g : Ω → ℝ) (h : Continuous g) : Integrable g μ :=
    h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have hu := integ u ((hq.mul continuous_const).mul (hf.comp hF))
  have hv := integ v ((hq.mul hchiPlus).mul (hgg.comp hF))
  have hz := integ z ((hq.mul hchiMinus).mul (hg₁.comp hF))
  have split : (fun y => q y * twoStripProfile F chiPlus chiMinus ρ K y * f (F y)) =
      fun y => (u y + v y) + z y := by
    funext y
    dsimp [u, v, z, g₁, g₂, twoStripProfile]
    ring
  rw [split]
  have hsum := integral_add (hu.add hv) hz
  simp only [Pi.add_apply] at hsum
  rw [hsum, integral_add hu hv]
  have hv' : (∫ y, v y ∂μ) = ∫ t, η t * (g₁ t + g₂ t) := identityPlus _ hgg
  have hz' : (∫ y, z y ∂μ) = -(∫ t, η t * g₁ t) := identityMinus _ hg₁
  rw [hv', hz']
  have intmul (g : ℝ → ℝ) (h : Continuous g) : Integrable (fun t => η t * g t) :=
    (hη.mul h).integrable_of_hasCompactSupport suppη.mul_right
  simp_rw [mul_add]
  rw [integral_add (intmul g₁ hg₁) (intmul g₂ hg₂)]
  have eqn : (∫ t, η t * g₂ t) = ∫ t, f t * ρ t := by
    apply integral_congr_ae
    filter_upwards with t
    dsimp [g₂]
    rw [← mul_assoc, support, mul_comm]
  rw [eqn]
  change (∫ y, u y ∂μ) + ((∫ t, η t * g₁ t) + ∫ t, f t * ρ t) +
      -(∫ t, η t * g₁ t) = (∫ y, u y ∂μ) + ∫ t, f t * ρ t
  ring

end VenRateUpper
