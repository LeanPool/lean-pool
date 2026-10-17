/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.BallForcing
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.MeanSquareDeviation

/-!
# BallAverage

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Value at a centre from an `L²` bound and a Hölder modulus

A continuous representative whose oscillation on a ball is controlled by a
Hölder modulus has its value at the centre controlled by the `L²` average of
the function on that ball plus the modulus.  This is the step that converts an
`L²` smallness statement into a pointwise one.

## Main results

- `DivergenceFormProcess.Decay.integral_abs_le_sqrt_mul_sqrt`
- `DivergenceFormProcess.Decay.abs_center_le_of_holder`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

variable {d : ℕ}

/-- Cauchy--Schwarz against the constant one, in the elementary Young form. -/
theorem integral_abs_le_sqrt_mul_sqrt {mu : Measure (Vec d)} [IsFiniteMeasure mu]
    {w : Vec d → ℝ} (hw : Integrable w mu)
    (hw2 : Integrable (fun y => w y ^ 2) mu) :
    (∫ y, |w y| ∂mu) ≤
      Real.sqrt ((mu Set.univ).toReal) * Real.sqrt (∫ y, w y ^ 2 ∂mu) := by
  set V : ℝ := (mu Set.univ).toReal with hV
  set S : ℝ := ∫ y, w y ^ 2 ∂mu with hS
  have hVnn : 0 ≤ V := ENNReal.toReal_nonneg
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => sq_nonneg _)
  rcases eq_or_lt_of_le hSnn with hS0 | hSpos
  · have hsq : (fun y => w y ^ 2) =ᵐ[mu] 0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae ?_ hw2).1 hS0.symm
      exact Filter.Eventually.of_forall fun y => sq_nonneg _
    have hzero : (fun y => |w y|) =ᵐ[mu] 0 := by
      filter_upwards [hsq] with y hy
      have hy2 : w y ^ 2 = 0 := hy
      simp only [Pi.zero_apply, abs_eq_zero]
      exact sq_eq_zero_iff.1 hy2
    rw [integral_congr_ae hzero]
    simp only [Pi.zero_apply, integral_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · set t : ℝ := Real.sqrt V / Real.sqrt S with ht
    have hsqrtS : 0 < Real.sqrt S := Real.sqrt_pos.2 hSpos
    have hyoung : ∀ y, |w y| ≤ (t * w y ^ 2 + Real.sqrt S / Real.sqrt V * 1) / 2 ∨
        Real.sqrt V = 0 := by
      intro y
      by_cases hVzero : Real.sqrt V = 0
      · exact Or.inr hVzero
      · left
        have hsqrtV : 0 < Real.sqrt V :=
          lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hVzero)
        have ht0 : 0 < t := div_pos hsqrtV hsqrtS
        have hkey : 0 ≤ (Real.sqrt t * |w y| - 1 / Real.sqrt t) ^ 2 := sq_nonneg _
        have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
        have habs : |w y| ^ 2 = w y ^ 2 := sq_abs _
        have hinv : Real.sqrt t * (1 / Real.sqrt t) = 1 := by
          field_simp
        have hexpand : (Real.sqrt t * |w y| - 1 / Real.sqrt t) ^ 2 =
            t * w y ^ 2 - 2 * |w y| + (1 / Real.sqrt t) ^ 2 := by
          have : (Real.sqrt t * |w y| - 1 / Real.sqrt t) ^ 2 =
              Real.sqrt t ^ 2 * |w y| ^ 2 -
                2 * (Real.sqrt t * (1 / Real.sqrt t)) * |w y| +
                (1 / Real.sqrt t) ^ 2 := by ring
          rw [this, hsq, habs, hinv]
          ring
        have hinvt : (1 / Real.sqrt t) ^ 2 = Real.sqrt S / Real.sqrt V := by
          rw [div_pow, one_pow, hsq, ht]
          rw [one_div_div]
        rw [hexpand, hinvt] at hkey
        linarith only [hkey]
    have hVpos : 0 < V := by
      by_contra hcon
      have hV0 : V = 0 := le_antisymm (not_lt.1 hcon) hVnn
      have : mu Set.univ = 0 := by
        have hne : mu Set.univ ≠ ⊤ := measure_ne_top mu Set.univ
        exact (ENNReal.toReal_eq_zero_iff _).1 hV0 |>.resolve_right hne
      have hSzero : S = 0 := by
        rw [hS]
        rw [show mu = 0 from Measure.measure_univ_eq_zero.1 this]
        simp
      exact absurd hSzero hSpos.ne'
    have hsqrtV : 0 < Real.sqrt V := Real.sqrt_pos.2 hVpos
    have hbound : ∀ y, |w y| ≤ (t * w y ^ 2 + Real.sqrt S / Real.sqrt V) / 2 := by
      intro y
      rcases hyoung y with h | h
      · simpa only [mul_one] using h
      · exact absurd h hsqrtV.ne'
    have hint : (∫ y, |w y| ∂mu) ≤
        ∫ y, (t * w y ^ 2 + Real.sqrt S / Real.sqrt V) / 2 ∂mu := by
      refine integral_mono_ae hw.abs ?_ (Filter.Eventually.of_forall hbound)
      exact ((hw2.const_mul t).add (integrable_const _)).div_const 2
    have hcomp : (∫ y, (t * w y ^ 2 + Real.sqrt S / Real.sqrt V) / 2 ∂mu) =
        (t * S + V * (Real.sqrt S / Real.sqrt V)) / 2 := by
      rw [integral_div, integral_add (hw2.const_mul t) (integrable_const _),
        integral_const_mul, integral_const, ← hS]
      simp only [smul_eq_mul, measureReal_def]
      rw [← hV]
    have hts : t * S = Real.sqrt V * Real.sqrt S := by
      have hrw : t * S = Real.sqrt V * (S / Real.sqrt S) := by rw [ht]; ring
      rw [hrw, Real.div_sqrt]
    have hvs : V * (Real.sqrt S / Real.sqrt V) = Real.sqrt V * Real.sqrt S := by
      have hrw : V * (Real.sqrt S / Real.sqrt V) =
          Real.sqrt S * (V / Real.sqrt V) := by ring
      rw [hrw, Real.div_sqrt]
      ring
    rw [hcomp, hts, hvs] at hint
    calc
      (∫ y, |w y| ∂mu) ≤
          (Real.sqrt V * Real.sqrt S + Real.sqrt V * Real.sqrt S) / 2 := hint
      _ = Real.sqrt V * Real.sqrt S := by ring

/-- The value of a continuous representative at the centre of a ball is bounded
by the `L²` average of an almost-everywhere equal function plus the Hölder
modulus on that ball. -/
theorem abs_center_le_of_holder [NeZero d]
    {x₀ : Vec d} {rho K alpha : ℝ} (hrho : 0 < rho) {v w : Vec d → ℝ}
    (hHolder : ∀ y ∈ euclideanBall x₀ rho, |v x₀ - v y| ≤ K * rho ^ alpha)
    (hae : v =ᵐ[volume.restrict (euclideanBall x₀ rho)] w)
    (hw : MemLp w 2 (volume.restrict (euclideanBall x₀ rho))) :
    |v x₀| ≤
      Real.sqrt (∫ y in euclideanBall x₀ rho, w y ^ 2 ∂volume) /
          Real.sqrt ((volume (smallContrastUnitBall d)).toReal * rho ^ d) +
        K * rho ^ alpha := by
  classical
  set B : Set (Vec d) := euclideanBall x₀ rho with hBdef
  set mu : Measure (Vec d) := volume.restrict B with hmudef
  have hBmeas : MeasurableSet B := (isOpen_euclideanBall x₀ rho).measurableSet
  have : IsFiniteMeasure mu :=
    HCPolySupport.Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall x₀ rho
  have hVeq : (volume B).toReal =
      (volume (smallContrastUnitBall d)).toReal * rho ^ d :=
    volume_euclideanBall_toReal_eq_unit_mul_pow x₀ hrho
  have hVne : (volume B).toReal ≠ 0 := HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero
    x₀ hrho
  have hVpos : 0 < (volume B).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hVne)
  have hunivB : (mu Set.univ).toReal = (volume B).toReal := by
    rw [hmudef, Measure.restrict_apply_univ]
  have hwInt : Integrable w mu := hw.integrable (by norm_num)
  have hw2Int : Integrable (fun y => w y ^ 2) mu :=
    (memLp_two_iff_integrable_sq hw.aestronglyMeasurable).1 hw
  have hmem : ∀ᵐ y ∂mu, y ∈ B :=
    (ae_restrict_iff' hBmeas).2 (Filter.Eventually.of_forall fun _ hy => hy)
  have hstep1 : ∀ᵐ y ∂mu, |v x₀| ≤ |w y| + K * rho ^ alpha := by
    filter_upwards [hmem, hae] with y hy hvy
    have hosc := hHolder y hy
    have h1 : |v x₀| ≤ |v y| + |v x₀ - v y| := by
      have hsub := abs_sub_abs_le_abs_sub (v x₀) (v y)
      linarith only [hsub]
    rw [hvy] at h1 hosc
    linarith only [h1, hosc]
  have hstep2 : (volume B).toReal * |v x₀| ≤
      (∫ y, |w y| ∂mu) + (volume B).toReal * (K * rho ^ alpha) := by
    have hmono := integral_mono_ae (integrable_const |v x₀|)
      (hwInt.abs.add (integrable_const (K * rho ^ alpha))) hstep1
    simp only [Pi.add_apply] at hmono
    rw [integral_add hwInt.abs (integrable_const _), integral_const,
      integral_const] at hmono
    simp only [smul_eq_mul, measureReal_def, hunivB] at hmono
    exact hmono
  have hstep3 : (∫ y, |w y| ∂mu) ≤
      Real.sqrt ((volume B).toReal) * Real.sqrt (∫ y, w y ^ 2 ∂mu) := by
    have := integral_abs_le_sqrt_mul_sqrt hwInt hw2Int
    rwa [hunivB] at this
  have hsqrtV : 0 < Real.sqrt ((volume B).toReal) := Real.sqrt_pos.2 hVpos
  have hVsq : Real.sqrt ((volume B).toReal) * Real.sqrt ((volume B).toReal) =
      (volume B).toReal := Real.mul_self_sqrt hVpos.le
  have hcomb : (volume B).toReal * |v x₀| ≤
      Real.sqrt ((volume B).toReal) * Real.sqrt (∫ y, w y ^ 2 ∂mu) +
        (volume B).toReal * (K * rho ^ alpha) := by
    linarith only [hstep2, hstep3]
  have hcomb' : Real.sqrt ((volume B).toReal) *
      (Real.sqrt ((volume B).toReal) * |v x₀|) ≤
        Real.sqrt ((volume B).toReal) *
          (Real.sqrt (∫ y, w y ^ 2 ∂mu) +
            Real.sqrt ((volume B).toReal) * (K * rho ^ alpha)) := by
    have hl : Real.sqrt ((volume B).toReal) *
        (Real.sqrt ((volume B).toReal) * |v x₀|) =
          (volume B).toReal * |v x₀| := by
      rw [← mul_assoc, hVsq]
    have hr : Real.sqrt ((volume B).toReal) *
        (Real.sqrt (∫ y, w y ^ 2 ∂mu) +
          Real.sqrt ((volume B).toReal) * (K * rho ^ alpha)) =
          Real.sqrt ((volume B).toReal) * Real.sqrt (∫ y, w y ^ 2 ∂mu) +
            (volume B).toReal * (K * rho ^ alpha) := by
      rw [mul_add, ← mul_assoc, hVsq]
    rw [hl, hr]
    exact hcomb
  have hcancel := le_of_mul_le_mul_left hcomb' hsqrtV
  have hfinal : |v x₀| ≤
      Real.sqrt (∫ y, w y ^ 2 ∂mu) / Real.sqrt ((volume B).toReal) +
        K * rho ^ alpha := by
    have hstep : |v x₀| - K * rho ^ alpha ≤
        Real.sqrt (∫ y, w y ^ 2 ∂mu) / Real.sqrt ((volume B).toReal) := by
      rw [le_div_iff₀ hsqrtV]
      linarith only [hcancel]
    linarith only [hstep]
  rw [hVeq] at hfinal
  exact hfinal

end DivergenceFormProcess.Decay
