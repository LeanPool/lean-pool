/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupEnergyWeighted
public import Mathlib.Analysis.MeanInequalities

public section

open CKN CKN.Foundation.Parabolic MeasureTheory
open scoped ENNReal
noncomputable section
namespace ESS

/-- The three terms in the cutoff energy bound are integrable under the
velocity `L³` and pressure `L^(3/2)` assumptions on a finite region. -/
theorem blowupEnergyMajorant_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (U p : α → ℝ)
    (hU : MemLp U 3 μ) (hp : MemLp p (3 / 2 : ℝ≥0∞) μ)
    (C : ℝ) :
    Integrable (fun z =>
      (8 + 3 * C) * (U z) ^ 2 + 3 * C * (U z) ^ 3 +
        6 * C * |p z| * U z) μ := by
  have hU2 : MemLp U 2 μ := hU.mono_exponent (by norm_num)
  have hsq : Integrable (fun z => U z ^ 2) μ := hU2.integrable_sq
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have : ENNReal.HolderTriple 3 3 (3 / 2 : ℝ≥0∞) := by
    have h : (3 : ℝ).HolderTriple 3 (3 / 2 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    simpa only [hcoeff, show ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) by norm_num]
      using h.ennrealOfReal
  have : ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) 3 1 := by
    have h : (3 / 2 : ℝ).HolderTriple 3 1 := by
      rw [Real.holderTriple_iff]
      norm_num
    simpa only [hcoeff, show ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) by norm_num,
      show ENNReal.ofReal (1 : ℝ) = (1 : ℝ≥0∞) by norm_num]
      using h.ennrealOfReal
  have hU_sq : MemLp (fun z => U z * U z) (3 / 2 : ℝ≥0∞) μ := by
    exact hU.mul hU
  have hU_cube : MemLp (fun z => U z * U z * U z) 1 μ := by
    exact hU_sq.mul hU
  have hcube : Integrable (fun z => U z ^ 3) μ := by
    have hh := hU_cube.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    have heq : (fun z => U z ^ 3) = (fun z => U z * U z * U z) := by
      funext z
      ring
    rw [heq]
    exact hh
  have hpabs : MemLp (fun z => |p z|) (3 / 2 : ℝ≥0∞) μ := by
    simpa only [Real.norm_eq_abs] using hp.norm
  have hpu : Integrable (fun z => |p z| * U z) μ := by
    have hmul : MemLp (fun z => |p z| * U z) 1 μ := by
      exact hpabs.mul hU
    exact hmul.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  have hsum := ((hsq.const_mul (8 + 3 * C)).add
    (hcube.const_mul (3 * C))).add (hpu.const_mul (6 * C))
  convert hsum using 1
  ext z
  simp only [Pi.add_apply]
  ring

/-- A bounded spatial ball and a finite past time interval have finite
space-time volume. -/
theorem blowupEnergyOuter_finiteMeasure (R a : ℝ) (hR : 0 < R) :
    IsFiniteMeasure
      ((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Set.Ioo (a - 2) 0))) := by
  constructor
  rw [Measure.restrict_apply_univ,
    CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  change (volume.prod volume)
    (CKN.euclideanBall 0 (R + 1) ×ˢ Set.Ioo (a - 2) 0) < ⊤
  rw [Measure.prod_prod]
  exact ENNReal.mul_lt_top
    (CKN.volume_euclideanBall_lt_top 0 (by linarith only [hR]))
    (by simp)

/-- The energy majorant is bounded by a constant, cubic velocity mass,
and pressure `3/2` mass. -/
theorem blowupEnergyMajorant_le_cubic_pressure
    (C U p : ℝ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    (8 + 3 * C) * U ^ 2 + 3 * C * U ^ 3 + 6 * C * |p| * U ≤
      (8 + 3 * C) + (8 + 8 * C) * U ^ 3 +
        4 * C * |p| ^ (3 / 2 : ℝ) := by
  have hU2 : U ^ 2 ≤ 1 + U ^ 3 := by
    by_cases hsmall : U ≤ 1
    · have hs : U ^ 2 ≤ 1 := by nlinarith only [hU, hsmall]
      nlinarith only [hs, pow_nonneg hU 3]
    · have hlarge : 1 ≤ U := le_of_not_ge hsmall
      nlinarith only [hU, hlarge, sq_nonneg U]
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hyoung := Real.young_inequality_of_nonneg (abs_nonneg p) hU hpq
  have hyoung' : |p| * U ≤
      (2 / 3 : ℝ) * |p| ^ (3 / 2 : ℝ) + (1 / 3 : ℝ) * U ^ 3 := by
    convert hyoung using 1
    · norm_num [Real.rpow_natCast]
      ring
  have hA : 0 ≤ 8 + 3 * C := by positivity
  have hB : 0 ≤ 6 * C := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hU2 hA
  have hthird := mul_le_mul_of_nonneg_left hyoung' hB
  nlinarith only [hfirst, hthird]

end ESS
